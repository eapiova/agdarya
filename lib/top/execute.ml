open Bwd
open Util
open Core
open Origin
open Reporter
open Parser
open PPrint
open Print
module Trie = Yuujinchou.Trie

(* Execution of files (and strings), including marshaling and unmarshaling, and managing file identifiers and imports. *)

(* Compiled files are tagged with the git hash of the commit, so they will only be loaded by Agdarya built from the exact same commit.  This is overkill, since most commits don't change the marshaling format; but it guarantees automatically that we never try to load a file that has a different marshaling format, thereby avoiding segmentation faults.  A version of -1 means that we don't know our git commit, and therefore we never load or save compiled files. *)
let __COMPILE_VERSION__ =
  Option.value ~default:(-1) (int_of_string_opt ("0x" ^ [%blob "version.txt"]))

(* This state module is for data that gets restarted when loading a new file. *)
module Loadstate = struct
  type t = {
    (* The current directory.  Used for making filenames absolute. *)
    cwd : FilePath.filename;
    (* All files whose loading is currently in progress, i.e. the path of imports that led us to the current file.  Used to check for circular imports. *)
    parents : FilePath.filename Bwd.t;
    (* All the files imported so far by the current file, *transitively* (that is, files it imports, and files *they* import, etc.).  Stored in compiled files to ensure they are recompiled whenever any dependencies change, and for linking purposes. *)
    imports : (File.t * FilePath.filename) Bwd.t;
    (* Whether the current file has performed any effectual actions like 'echo'.  Stored in compiled files to produce a warning. *)
    actions : bool;
  }
end

module Loading = struct
  include State.Make (Loadstate)

  let run ~init f =
    run ~init @@ fun () ->
    try f ()
    with effect Parser.Command.Chdir dir, k ->
      let cwd = FilePath.make_absolute (get ()).cwd dir in
      modify (fun s -> { s with cwd });
      Effect.Deep.continue k cwd
end

let () =
  Loading.register_printer (function
    | `Get -> Some "unhandled Loading.get effect"
    | `Set _ -> Some "unhandled Loading.set effect")

(* This reader module is for data that's supplied by the executable, mostly from the command-line, and doesn't change. *)
module FlagData = struct
  type t = {
    (* Marshal all the command-line type theory flags to disk. *)
    marshal : Out_channel.t -> unit;
    (* Unmarshal all the command-line type theory flags from a disk file and check that they agree with the current ones, returning the unmarshaled ones if not. *)
    unmarshal : In_channel.t -> (unit, string) Result.t;
    (* Load files from source only (not compiled versions). *)
    source_only : bool;
    (* All the filenames given explicitly on the command line. *)
    top_files : string list;
    (* Whether to reformat explicitly-loaded files *)
    reformat : bool;
  }
end

module Flags = Algaeff.Reader.Make (FlagData)

let () = Flags.register_printer (function `Read -> Some "unhandled Flags.read effect")

module Loaded = struct
  type data = {
    trie : Scope.trie;
    globals : Global.origin_entry;
    file : File.t;
    old_imports : (File.t * FilePath.filename) Bwd.t;
    explicit : bool;
  }

  type _ Effect.t +=
    | Add_to_files : FilePath.filename * data -> unit Effect.t
    | Get_file : FilePath.filename -> (data * float) option Effect.t
    | Add_to_scope : Scope.trie -> unit Effect.t
    | Get_scope : Scope.trie Effect.t

  open Effect.Deep

  let run f =
    (* All the files that have been loaded so far in this run of the program, along with their export namespaces, file identifiers, files that *they* import transitively, modification time when they were loaded, and whether they were explicitly invoked on the command line. *)
    let loaded_files : (FilePath.filename, data * float) Hashtbl.t = Hashtbl.create 20 in
    (* The complete merged namespace of all the files explicitly given on the command line so far.  Imported into -e and -i.  We compute it lazily because if there is no -e or -i we don't need it.  (And also so that we won't try to read the flags before they're set.)  It starts as the "current" namespace, which should be the top-level one. *)
    let loaded_contents : Scope.trie Lazy.t ref = ref (Lazy.from_val (Scope.get_visible ())) in
    try f () with
    | effect Add_to_files (file, data), k ->
        let mtime = (FileUtil.stat file).modification_time in
        Hashtbl.add loaded_files file (data, mtime);
        continue k ()
    | effect Get_file file, k -> continue k (Hashtbl.find_opt loaded_files file)
    | effect Add_to_scope trie, k ->
        let old = !loaded_contents in
        loaded_contents := lazy (Scope.Mod.union ~prefix:Emp (Lazy.force old) trie);
        continue k ()
    (* Add something to the complete merged namespace. *)
    | effect Get_scope, k -> continue k (Lazy.force !loaded_contents)

  let add_to_scope trie = Effect.perform (Add_to_scope trie)
  let get_scope () = Effect.perform Get_scope
  let get_file file = Effect.perform (Get_file file)

  let add_to_files filename trie globals file old_imports explicit =
    Effect.perform (Add_to_files (filename, { trie; globals; file; old_imports; explicit }))
end

type pending_defs = {
  cmds : Parser.Command.t list;
  existing : Core.Constant.t Parser.Command.StringsMap.t;
}

let ordinary_pending : pending_defs option ref = ref None

let rec flush_pending_commands () =
  match !ordinary_pending with
  | None -> ()
  | Some { cmds; existing } ->
      ordinary_pending := None;
      let defs = Parser.Command.defs_of_pending_commands cmds in
      let exec_defs =
        match Origin.current () with
        | Instant _ -> Parser.Command.exec_defs_current
        | Top | File _ -> Parser.Command.exec_defs in
      ignore (exec_defs ~existing defs);
      ()

and enqueue_ordinary_command cmd =
  let ordinary_source_head existing =
    Parser.Command.ordinary_source_head ~prefer_ordinary:(fun name -> Parser.Command.StringsMap.mem name existing) cmd
  in
  (match (!ordinary_pending, Option.bind !ordinary_pending (fun pending -> ordinary_source_head pending.existing)) with
  | Some { cmds; existing }, Some (name, _) when not (Parser.Command.StringsMap.mem name existing) ->
      let shadows_existing_syntax =
        Parser.Scope.lookup_field name <> None || Parser.Scope.lookup_constr name <> None
      in
      if
        shadows_existing_syntax
        ||
        (Parser.Command.pending_commands_are_complete cmds
        && not (Parser.Command.pending_commands_reference_name cmds name))
      then flush_pending_commands ()
  | _ -> ());
  let pending =
    match !ordinary_pending with
    | Some pending -> pending
    | None -> { cmds = []; existing = Parser.Command.StringsMap.empty } in
  let existing =
    match ordinary_source_head pending.existing with
    | Some (name, loc) when not (Parser.Command.StringsMap.mem name pending.existing) ->
        let const = Parser.Command.predeclare_constant ?loc name in
        Parser.Command.StringsMap.add name const pending.existing
    | _ -> pending.existing in
  Parser.Command.predeclare_ordinary_syntax cmd existing;
  ordinary_pending := Some { cmds = pending.cmds @ [ cmd ]; existing }

let source_contents (source : Asai.Range.source) =
  match source with
  | `String { content; _ } -> content
  | `File filename ->
      In_channel.with_open_bin filename @@ fun chan ->
      really_input_string chan (Int64.to_int (In_channel.length chan))

let split_lines_preserving_newlines content =
  let len = String.length content in
  let rec go i j acc =
    if j = len then
      if i = len then List.rev acc else List.rev (String.sub content i (len - i) :: acc)
    else if content.[j] = '\n' then
      go (j + 1) (j + 1) (String.sub content i (j - i + 1) :: acc)
    else go i (j + 1) acc
  in
  go 0 0 []

let indent_of_line line =
  let rec go i =
    if i < String.length line && (line.[i] = ' ' || line.[i] = '\t') then go (i + 1) else i
  in
  go 0

let starts_with s prefix =
  let lp = String.length prefix in
  String.length s >= lp && String.sub s 0 lp = prefix

let is_word_boundary s i =
  i >= String.length s
  ||
  match s.[i] with
  | ' ' | '\t' | '\n' | '\r' | '(' | '{' | '"' -> true
  | _ -> false

let has_sig_or_clause_marker line =
  let len = String.length line in
  let rec go i =
    i < len
    &&
    match line.[i] with
    | ':' | '=' -> true
    | _ -> go (i + 1)
  in
  go 0

let reserved_command_keywords =
  [
    "postulate";
    "echo";
    "synth";
    "notation";
    "infixl";
    "infixr";
    "infix";
    "import";
    "export";
    "section";
    "end";
    "data";
    "record";
    "display";
    "solve";
    "split";
    "show";
    "fmt";
    "undo";
    "quit";
    "chdir";
    "module";
    "open";
    "private";
    "public";
  ]

let starts_reserved_command trimmed =
  List.exists
    (fun kw -> starts_with trimmed kw && is_word_boundary trimmed (String.length kw))
    reserved_command_keywords

type chunk_start_kind = [ `Header | `Sig_or_clause ]

let command_start_kind line =
  let indent = indent_of_line line in
  let trimmed =
    if indent >= String.length line then "" else String.sub line indent (String.length line - indent) in
  if trimmed = "" then None
  else if starts_with trimmed "{-#" then Some `Header
  else if starts_reserved_command trimmed then Some `Header
  else
    match trimmed.[0] with
    | '|' | ']' | ')' | '}' | ',' | '.' | '-' -> None
    | _ -> if has_sig_or_clause_marker trimmed then Some `Sig_or_clause else None

let is_command_start_line line = Option.is_some (command_start_kind line)

let line_is_blank line =
  let indent = indent_of_line line in
  let trimmed =
    if indent >= String.length line then "" else String.sub line indent (String.length line - indent) in
  String.trim trimmed = ""

type split_scan_state = {
  block_comment_depth : int;
  nesting_depth : int;
  guillemet_depth : int;
  in_string : bool;
  escaped : bool;
}

let initial_split_scan_state =
  { block_comment_depth = 0; nesting_depth = 0; guillemet_depth = 0; in_string = false; escaped = false }

let utf8_guillemet_start = "\xC2\xAB"
let utf8_guillemet_end = "\xC2\xBB"

let starts_with_utf8 s i piece =
  let lp = String.length piece in
  i + lp <= String.length s && String.sub s i lp = piece

let sanitize_line_for_split state line =
  let len = String.length line in
  let buf = Bytes.of_string line in
  let blank_range i j =
    for k = i to j - 1 do
      if k < len && line.[k] <> '\n' then Bytes.set buf k ' '
    done
  in
  let blank_rest i = blank_range i len in
  let rec go i state =
    if i >= len then state
    else if state.block_comment_depth > 0 then
      if i + 1 < len && line.[i] = '{' && line.[i + 1] = '-' then (
        blank_range i (i + 2);
        go (i + 2) { state with block_comment_depth = state.block_comment_depth + 1 })
      else if i + 1 < len && line.[i] = '-' && line.[i + 1] = '}' then (
        blank_range i (i + 2);
        go (i + 2) { state with block_comment_depth = state.block_comment_depth - 1 })
      else (
        blank_range i (i + 1);
        go (i + 1) state)
    else if state.guillemet_depth > 0 then
      if starts_with_utf8 line i utf8_guillemet_start then
        go (i + 2) { state with guillemet_depth = state.guillemet_depth + 1 }
      else if starts_with_utf8 line i utf8_guillemet_end then
        go (i + 2) { state with guillemet_depth = state.guillemet_depth - 1 }
      else
        go (i + 1) state
    else if state.in_string then (
      blank_range i (i + 1);
      if state.escaped then
        go (i + 1) { state with escaped = false }
      else
        match line.[i] with
        | '\\' -> go (i + 1) { state with escaped = true }
        | '"' -> go (i + 1) { state with in_string = false }
        | _ -> go (i + 1) state)
    else if i + 2 < len && line.[i] = '{' && line.[i + 1] = '-' && line.[i + 2] = '#' then
      go (i + 3) state
    else if i + 1 < len && line.[i] = '{' && line.[i + 1] = '-' then (
      blank_range i (i + 2);
      go (i + 2) { state with block_comment_depth = 1 })
    else if i + 1 < len && line.[i] = '-' && line.[i + 1] = '-' then (
      blank_rest i;
      state)
    else if starts_with_utf8 line i utf8_guillemet_start then
      go (i + 2) { state with guillemet_depth = 1 }
    else if line.[i] = '"' then (
      blank_range i (i + 1);
      go (i + 1) { state with in_string = true; escaped = false })
    else if line.[i] = '(' || line.[i] = '[' || line.[i] = '{' then
      go (i + 1) { state with nesting_depth = state.nesting_depth + 1 }
    else if line.[i] = ')' || line.[i] = ']' || line.[i] = '}' then
      go (i + 1) { state with nesting_depth = max 0 (state.nesting_depth - 1) }
    else
      go (i + 1) state
  in
  let state = go 0 state in
  (Bytes.to_string buf, state)

let trimmed_last_char s =
  let rec go i =
    if i < 0 then None
    else
      match s.[i] with
      | ' ' | '\t' | '\n' | '\r' -> go (i - 1)
      | c -> Some c
  in
  go (String.length s - 1)

let contains_substring s sub =
  let ls = String.length s and lsub = String.length sub in
  let rec go i =
    i + lsub <= ls && (String.sub s i lsub = sub || go (i + 1))
  in
  lsub = 0 || go 0

let first_nonblank_line s =
  let rec go = function
    | [] -> ""
    | line :: lines ->
        let indent = indent_of_line line in
        let trimmed =
          if indent >= String.length line then "" else String.sub line indent (String.length line - indent)
        in
        if String.trim trimmed = "" then go lines else trimmed
  in
  go (split_lines_preserving_newlines s)

let chunk_expects_continuation current_kind buf =
  match trimmed_last_char (Buffer.contents buf) with
  | Some ('=' | ':') -> true
  | _ -> (
      match current_kind with
      | `Sig_or_clause -> false
      | `Header ->
          let contents = Buffer.contents buf in
          let first = first_nonblank_line contents in
          ((starts_with first "record" && is_word_boundary first (String.length "record"))
          || (starts_with first "data" && is_word_boundary first (String.length "data"))
          || (starts_with first "module" && is_word_boundary first (String.length "module")))
          && not (contains_substring contents "where"))

let split_source_commands_with_boundaries content =
  let lines = split_lines_preserving_newlines content in
  let prelude = Buffer.create 128 in
  let current = ref None in
  let chunks = ref [] in
  let state = ref initial_split_scan_state in
  let flush_current () =
    match !current with
    | None -> ()
    | Some (buf, indent, _) ->
        ignore indent;
        chunks := Buffer.contents buf :: !chunks;
        current := None
  in
  List.iter
    (fun line ->
      let start_state = !state in
      let sanitized, next_state = sanitize_line_for_split !state line in
      state := next_state;
      let indent = indent_of_line line in
      let trimmed =
        if indent >= String.length line then "" else String.sub line indent (String.length line - indent) in
      let inside_construct =
        start_state.block_comment_depth > 0
        || start_state.guillemet_depth > 0
        || start_state.in_string
        || start_state.nesting_depth > 0 in
      let start_kind =
        if inside_construct then None
        else
          match command_start_kind sanitized with
          | Some _ as kind -> kind
          | None when starts_reserved_command trimmed -> Some `Header
          | None -> None in
      let starts = Option.is_some start_kind in
      let blank = line_is_blank line && not inside_construct in
      match !current with
      | None ->
          if blank then
            ()
          else if starts then (
            let buf = Buffer.create (max 64 (String.length line)) in
            Buffer.add_buffer buf prelude;
            Buffer.clear prelude;
            Buffer.add_string buf line;
            current := Some (buf, indent, Option.get start_kind))
          else (
            Buffer.add_string prelude line)
      | Some (buf, current_indent, current_kind) ->
          if blank then (
            if chunk_expects_continuation current_kind buf then
              Buffer.add_string buf line
            else (
              flush_current ();
              Buffer.clear prelude))
          else if starts
                  && (current_kind = `Header || indent <= current_indent)
                  && not (chunk_expects_continuation current_kind buf)
          then (
            flush_current ();
            let buf = Buffer.create (max 64 (String.length line)) in
            Buffer.add_string buf line;
            current := Some (buf, indent, Option.get start_kind))
          else (
            Buffer.add_string buf line))
    lines;
  flush_current ();
  List.rev !chunks

let split_source_commands content =
  split_source_commands_with_boundaries content

let chunk_start_kind chunk =
  let lines = split_lines_preserving_newlines chunk in
  let rec go state = function
    | [] -> None
    | line :: lines ->
        let start_state = state in
        let sanitized, next_state = sanitize_line_for_split state line in
        let inside_construct =
          start_state.block_comment_depth > 0
          || start_state.guillemet_depth > 0
          || start_state.in_string
          || start_state.nesting_depth > 0 in
        if line_is_blank line && not inside_construct then go next_state lines
        else if inside_construct then go next_state lines
        else command_start_kind sanitized
  in
  go initial_split_scan_state lines

(* Save all the definitions from a given loaded file to a compiled disk file, along with other data such as the command-line type theory flags, the imported files, and the (supplied) export namespace. *)
let marshal (file : File.t) (filename : FilePath.filename) (trie : Scope.trie) =
  if __COMPILE_VERSION__ > 0 then
    let ofile = FilePath.replace_extension filename "nyo" in
    try
      Out_channel.with_open_bin ofile @@ fun chan ->
      Marshal.to_channel chan __COMPILE_VERSION__ [];
      (Flags.read ()).marshal chan;
      Marshal.to_channel chan file [];
      Marshal.to_channel chan (Loading.get ()).imports [];
      Global.to_channel_origin chan (File file) [];
      Parser.Scope.to_channel chan trie [];
      Marshal.to_channel chan (Loading.get ()).actions []
      (* Just emit a warning if we can't write the compiled version *)
    with Sys_error _ -> emit (Cant_write_compiled_file ofile)

(* Load a file from a compiled disk file, if possible.  Returns its export namespace, or None if loading from a compiled file failed. *)
let rec unmarshal (file : File.t) (lookup : FilePath.filename -> File.t)
    (filename : FilePath.filename) =
  let ofile = FilePath.replace_extension filename "nyo" in
  (* To load a compiled file, first of all both the compiled file and its source file must exist, and the compiled file must be not older than the source.  (If the source was reformatted at the time of compiling, they could be exactly the same age.) *)
  if
    FileUtil.test Is_file filename
    && FileUtil.test Is_file ofile
    && not (FileUtil.test (Is_older_than filename) ofile)
  then
    (* Now we can start loading things. *)
    In_channel.with_open_bin ofile @@ fun chan ->
    (* We check it was compiled with the same version as us. *)
    let old_version = (Marshal.from_channel chan : int) in
    if __COMPILE_VERSION__ > 0 && old_version = __COMPILE_VERSION__ then (
      (* We also check it was compiled with the same type theory flags as us. *)
      match (Flags.read ()).unmarshal chan with
      | Ok () ->
          let old_file = (Marshal.from_channel chan : File.t) in
          (* Now we make sure none of the files *it* imports (transitively) have been modified more recently than the compilation, and that they have all been compiled. *)
          let old_imports = (Marshal.from_channel chan : (File.t * FilePath.filename) Bwd.t) in
          if
            Bwd.for_all
              (fun (_, ifile) ->
                let oifile = FilePath.replace_extension filename "nyo" in
                FileUtil.test Is_file oifile
                && (not (FileUtil.test (Is_older_than ifile) oifile))
                && not (FileUtil.test (Is_newer_than ofile) ifile))
              old_imports
          then (
            (* If so, we load all those files (from their compiled versions, or make sure that they were already loaded) right away.  We don't need their returned namespaces, since we aren't typechecking our compiled file. *)
            Mbwd.miter
              (fun [ (_, ifile) ] ->
                let _ = load_file ifile false in
                ())
              [ old_imports ];
            (* We create a hashtable mapping the old files to new ones. *)
            let table = Hashtbl.create 20 in
            Mbwd.miter (fun [ (i, ifile) ] -> Hashtbl.add table i (lookup ifile)) [ old_imports ];
            Hashtbl.add table old_file file;
            let find_in_table x =
              Hashtbl.find_opt table x
              <|> Anomaly "missing file identifier while unmarshaling compiled file" in
            (* Now we load the definitions from the compiled file, replacing all the old files by the new ones. *)
            let unit_entry = Global.from_istream_origin find_in_table (Channel chan) (File file) in
            let trie = Parser.Scope.from_istream (Channel chan) find_in_table in
            (* We check whether the compiled file had any actions, and issue a warning if so *)
            if (Marshal.from_channel chan : bool) then emit (Actions_in_compiled_file ofile);
            Some (trie, unit_entry, old_imports))
          else None
      | Error flags ->
          emit (Incompatible_flags (filename, flags));
          None)
    else None
  else None

(* Load a file, possibly one specified on the command line, either from source or from a compiled version. *)
and load_file filename top =
  if not (FilePath.check_extension filename "ny") then fatal (Invalid_filename filename);
  (* We normalize the file path to a reduced absolute one, so we can use it for a hashtable key. *)
  let filename =
    if FilePath.is_relative filename then FilePath.make_absolute (Loading.get ()).cwd filename
    else filename in
  let filename = FilePath.reduce filename in
  match Loaded.get_file filename with
  | Some ({ trie; globals; file; old_imports; explicit = top' }, mtime) ->
      (* If we already loaded that file, first we check that neither it nor any of its imports have been modified more recently that when they were loaded. *)
      if (FileUtil.stat filename).modification_time > mtime then fatal (Library_modified filename);
      Bwd.iter
        (fun (_, f) ->
          if (FileUtil.stat filename).modification_time > mtime then fatal (Library_modified f))
        old_imports;
      (* We add it back into Global, and to the 'all' namespace if it wasn't already there. *)
      Global.add_file file globals;
      if top && not top' then (
        Loaded.add_to_scope trie;
        (* Ensure that it's marked as having been loaded explicitly. *)
        Loaded.add_to_files filename trie globals file old_imports true);
      (* We also add it to the list of things imported by the current ambient file.  TODO: Should that go in execute_command Import? *)
      Loading.modify (fun s -> { s with imports = Snoc (s.imports, (file, filename)) });
      (* Return its saved export namespace. *)
      trie
  | None ->
      (* Otherwise, we have to load it.  First we check for circular dependencies. *)
      (let parents = (Loading.get ()).parents in
       if Bwd.exists (fun x -> x = filename) parents then
         fatal (Circular_import (Bwd.to_list (Snoc (parents, filename)))));
      (* We make a name for it *)
      let file = File.make (`File filename) in
      (* Now we record it as a file that was imported by the current file. *)
      Loading.modify (fun s -> { s with imports = Snoc (s.imports, (file, filename)) });
      (* Then we load it, in its directory and with itself added to the list of parents. *)
      let rename i = (fst (Loaded.get_file i <|> Anomaly "missing file in load_file")).file in
      let trie, imports =
        Loading.run
          ~init:
            {
              cwd = FilePath.dirname filename;
              parents = Snoc ((Loading.get ()).parents, filename);
              imports = Emp;
              actions = false;
            }
        @@ fun () ->
        (* If there's a compiled version, and we aren't in source-only mode, and this file wasn't specified explicitly on the command-line, we try loading the compiled version. *)
        let trie, globals, old_imports, which =
          let flags = Flags.read () in
          match
            if flags.source_only || List.mem filename flags.top_files then None
            else unmarshal file rename filename
          with
          | Some (trie, globals, old_imports) -> (trie, globals, old_imports, `Compiled)
          | None ->
              (* If we are in source-only mode, or this file was specified explicitly on the command-line, or if unmarshal failed (e.g. the compiled file is outdated), we load it from source. *)
              if not top then emit (Loading_file filename);
              (* If reformatting is enabled, and this file was explicitly specified on the command line, create a buffer to hold its reformatting. *)
              let buf =
                if (Flags.read ()).reformat && List.mem filename flags.top_files then
                  Some (Buffer.create 100)
                else None in
              let renderer = Option.map (PPrint.ToBuffer.pretty 1.0 (Display.columns ())) buf in
              (* Parse and execute the file and save its exported trie and global definitions *)
              let exported, unsolved =
                execute_source ~holes_allowed:top file ?renderer (`File filename) in
              (match buf with
              | None -> ()
              | Some buf -> (
                  (* If the reformatted version didn't change, do nothing. *)
                  let infile = open_in_bin filename in
                  let oldstr =
                    Fun.protect ~finally:(fun () -> close_in infile) @@ fun () ->
                    really_input_string infile (in_channel_length infile) in
                  if oldstr <> Buffer.contents buf then
                    try
                      (* Back up the original file to a new backup file name. *)
                      let bakfile, n = (filename ^ ".bak.", ref 0) in
                      while FileUtil.test Is_file (bakfile ^ string_of_int !n) do
                        n := !n + 1
                      done;
                      let bakfile = bakfile ^ string_of_int !n in
                      FileUtil.cp [ filename ] bakfile;
                      (* Overwrite the file with its reformatted version. *)
                      let outfile = open_out filename in
                      Fun.protect ~finally:(fun () -> close_out outfile) @@ fun () ->
                      output_string outfile (Buffer.contents buf)
                      (* Ignore file errors (e.g. read-only source file) *)
                    with Sys_error _ -> ()));
              (* Save the compiled version, if it contains no holes (holes contain a functional value). *)
              if unsolved = 0 then marshal file filename exported;
              (exported, Global.find_file file, (Loading.get ()).imports, `Source) in
        (* Then we add it to the table of loaded files and (possibly) the content of top-level files. *)
        if not top then emit (File_loaded (filename, which));
        Loaded.add_to_files filename trie globals file old_imports top;
        if top then Loaded.add_to_scope trie;
        (trie, (Loading.get ()).imports) in
      (* We add the files that it imports to those of the current file, since the imports list is supposed to be transitive. *)
      Loading.modify (fun s -> { s with imports = Bwd_extra.append s.imports imports });
      trie

(* Load an -e string or stdin. *)
and load_string ?init_visible title content =
  (* There is no caching and no change of state, since it can't be "required" from another file.  The caller specifies whether to use a special initial namespace. *)
  let file = File.make (`Other title) in
  let trie, _ =
    execute_source ~holes_allowed:true ?init_visible file (`String { title = Some title; content })
  in
  (* A string is always at top-level, so we always add it to 'all'. *)
  Loaded.add_to_scope trie;
  trie

(* Given a source (file or string), parse and execute all the commands in it, in a local scope that starts with either the supplied scope or a default one. *)
and execute_source ~holes_allowed ?init_visible ?renderer file (source : Asai.Range.source) =
  Origin.with_file ~holes_allowed file @@ fun () ->
  Option.iter Scope.set_visible init_visible;
  let render_command renderer cdns ws cmd =
    let new_cdns = Parser.Command.condense cmd in
    let ws =
      match renderer with
      | Some render ->
          let ws =
            if cdns = `Bof || (cdns <> `None && cdns = new_cdns) then
              Whitespace.normalize_no_blanks ws
            else Whitespace.normalize 2 ws in
          let space_before_starting_comment = if cdns = `Bof then Some 0 else None in
          let pcmd, wcmd = Parser.Command.pp_command cmd in
          render
            (pp_ws ?space_before_starting_comment (if cdns = `Bof then `None else `Cut) ws ^^ pcmd);
          wcmd
      | None -> [] in
    (new_cdns, ws)
  in
  let rec batch_fragment p src cdns ws =
    match Parser.Command.Parse.final p with
    | Eof -> (cdns, ws)
    | Bof prews ->
        let cdns, ws = if cdns = `None then (`Bof, prews) else (cdns, ws) in
        let p, src = Parser.Command.Parse.restart_parse p src in
        batch_fragment p src cdns ws
    | cmd ->
        let _ = execute_command cmd in
        let new_cdns, ws = render_command renderer cdns ws cmd in
        let p, src = Parser.Command.Parse.restart_parse p src in
        batch_fragment p src new_cdns ws
  in
  let rec exec_chunks ?title cdns ws = function
    | [] ->
        flush_pending_commands ();
        (match renderer with
        | Some render -> render (pp_ws `Cut ws)
        | None -> ())
    | chunk :: chunks -> (
        (match chunk_start_kind chunk with
        | Some `Header -> flush_pending_commands ()
        | Some `Sig_or_clause | None -> ());
        let too_many = ref false in
        let parsed = ref None in
        Reporter.try_with
          (fun () -> parsed := Some (Parser.Command.parse_single ?title chunk))
          ~fatal:(fun d ->
            match d.message with
            | Too_many_commands -> too_many := true
            | _ -> Reporter.fatal_diagnostic d);
        if !too_many then
          let src : Asai.Range.source = `String { content = chunk; title } in
          let p, src = Parser.Command.Parse.start_parse ~or_echo:true src in
          let new_cdns, ws = batch_fragment p src cdns ws in
          exec_chunks ?title new_cdns ws chunks
        else
          match !parsed with
          | Some (prews, Some cmd) ->
              let ws = if cdns = `None then prews else ws in
              let _ = execute_command cmd in
              let new_cdns, ws = render_command renderer cdns ws cmd in
              exec_chunks ?title new_cdns ws chunks
          | Some (_, None) | None -> exec_chunks ?title cdns ws chunks)
  in
  let run_source () =
    match source with
    | `String { title; _ } ->
        let chunks = split_source_commands_with_boundaries (source_contents source) in
        exec_chunks ?title `None [] chunks
    | `File name ->
        let chunks = split_source_commands_with_boundaries (source_contents source) in
        exec_chunks ~title:name `None [] chunks
  in
  Reporter.try_with run_source ~fatal:(fun d ->
      match d.message with
      | Quit _ ->
          let src =
            match source with
            | `File name -> Some name
            | `String { title; _ } -> title in
          Reporter.emit (Quit src)
      | _ -> Reporter.fatal_diagnostic d);
  (Scope.get_export (), Global.current_unsolved_holes ())

(* Parse, execute (if requested by Flags), and reformat (if requested by Flags) all the commands in a source. *)
and batch renderer p src cdns ws =
  let render_command renderer cdns ws cmd =
    let new_cdns = Parser.Command.condense cmd in
    let ws =
      match renderer with
      | Some render ->
          let ws =
            if cdns = `Bof || (cdns <> `None && cdns = new_cdns) then
              Whitespace.normalize_no_blanks ws
            else Whitespace.normalize 2 ws in
          let space_before_starting_comment = if cdns = `Bof then Some 0 else None in
          let pcmd, wcmd = Parser.Command.pp_command cmd in
          render
            (pp_ws ?space_before_starting_comment (if cdns = `Bof then `None else `Cut) ws ^^ pcmd);
          wcmd
      | None -> [] in
    (new_cdns, ws)
  in
  match Parser.Command.Parse.final p with
  | Eof -> (
      flush_pending_commands ();
      match renderer with
      | Some render -> render (pp_ws `Cut ws)
      | None -> ())
  | Bof ws ->
      let p, src = Parser.Command.Parse.restart_parse p src in
      batch renderer p src `Bof ws
  | cmd ->
      let _ = execute_command cmd in
      let new_cdns, ws = render_command renderer cdns ws cmd in
      let p, src = Parser.Command.Parse.restart_parse p src in
      batch renderer p src new_cdns ws

(* Wrapper around Parser.Command.execute that passes it the correct callbacks.  Does NOT check flags or reformat. *)
and execute_command cmd =
  let action_taken () = Loading.modify (fun s -> { s with actions = true }) in
  let get_file file = load_file file false in
  match cmd with
  | Parser.Command.TypeSig _ | Parser.Command.Clause _ ->
      enqueue_ordinary_command cmd;
      (None, [])
  | _ ->
      flush_pending_commands ();
      Parser.Command.execute ~action_taken ~get_file cmd
