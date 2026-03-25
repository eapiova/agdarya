open Bwd
open Bwd.Infix
open Dim
open Util
open List_extra
open Core
open Origin
open Readback
open Notation
open Postprocess
open Unparse
open Print
open Reporter
open User
open Modifier
open Printable
module Trie = Yuujinchou.Trie
module TermParse = Parse
open Asai.Range

type _ Effect.t += Chdir : string -> string Effect.t

module StringsMap = Map.Make (struct
  type t = string list

  let compare = compare
end)

module StringSet = Set.Make (String)

type 'a attribute = {
  wshash : Whitespace.t list;
  wslparen : Whitespace.t list;
  loc : Asai.Range.t option;
  attr : 'a;
  wsattr : Whitespace.t list list;
  wsrparen : Whitespace.t list;
}

type def_head =
  | Head_name of Trie.path
  | Head_notation :
      {
        fixity : ('left, 'tight, 'right) fixity;
        wslparen : Whitespace.t list;
        wstight : Whitespace.t list;
        wsellipsis : Whitespace.t list;
        wsrparen : Whitespace.t list;
        wspatlparen : Whitespace.t list;
        pattern : ('left, 'right) User.Pattern.t;
      }
      -> def_head

type def = {
  wsdef : Whitespace.t list;
  head : def_head;
  name : Trie.path;
  loc : Asai.Range.t option;
  wshead : Whitespace.t list;
  parameters : Parameter.t list;
  ty : (Whitespace.t list * wrapped_parse) option;
  wscoloneq : Whitespace.t list;
  tm : wrapped_parse;
}

type type_sig = {
  name : Trie.path;
  loc : Asai.Range.t option;
  wsname : Whitespace.t list;
  wscolon : Whitespace.t list;
  ty : wrapped_parse;
}

type local_cmd =
  | Local_type_sig of type_sig
  | Local_clause of clause

and where_block = {
  wswhere : Whitespace.t list;
  wslbrace : Whitespace.t list;
  first : local_cmd;
  rest : (Whitespace.t list * local_cmd) list;
  wsrbrace : Whitespace.t list;
}

and clause = {
  lhs : wrapped_parse;
  wseq : Whitespace.t list;
  tm : wrapped_parse;
  where_block : where_block option;
}

type module_name_list = {
  wslparen : Whitespace.t list;
  items : (Trie.path * Whitespace.t list) list;
  wsrparen : Whitespace.t list;
}

type module_renaming = {
  source : Trie.path;
  wssource : Whitespace.t list;
  wsto : Whitespace.t list;
  target : Trie.path;
  wstarget : Whitespace.t list;
}

type module_modifiers = {
  filter :
    [ `Using of Whitespace.t list * module_name_list
    | `Hiding of Whitespace.t list * module_name_list ]
    option;
  renaming : (Whitespace.t list * Whitespace.t list * module_renaming list * Whitespace.t list) option;
}

type extracted_record_field = string * wrapped_parse

let tokws t = (t, ([], None))

let build_outfix_tm notn parts =
  let obs =
    List.fold_left
      (fun obs -> function
        | `Tok tok -> Observations.snoc_tok obs (tokws tok)
        | `Term (Wrap tm) -> Observations.snoc_term obs tm)
      Observations.empty parts
  in
  Wrap (locate_opt None (outfix ~notn ~inner:(Observations.of_partial obs)))

let ident_tm x = Wrap (locate_opt None (Ident ([ x ], [])))

let synth_data_tm constrs =
  build_outfix_tm Builtins.data
    ([ `Tok Token.Data; `Tok Token.LBracket ]
    @ List.concat_map (fun tm -> [ `Tok (Token.Op "|"); `Term tm ]) constrs
    @ [ `Tok Token.RBracket ])

let synth_record_tm fields =
  let rec go = function
    | [] -> [ `Tok Token.RParen ]
    | [ (fld, ty) ] -> [ `Term (ident_tm fld); `Tok Token.Colon; `Term ty; `Tok Token.RParen ]
    | (fld, ty) :: fields ->
        [ `Term (ident_tm fld); `Tok Token.Colon; `Term ty; `Tok (Token.Op ",") ] @ go fields
  in
  build_outfix_tm Builtins.record ([ `Tok Token.Sig; `Tok Token.LParen ] @ go fields)

let rec strip_outer_parens (Wrap tm as wrapped) =
  match tm.value with
  | Notn ((Postprocess.Parens, _), n) -> (
      match args n with
      | [ Token (LParen, _); Term body; Token (RParen, _) ] -> strip_outer_parens (Wrap body)
      | _ -> wrapped)
  | _ -> wrapped

let extract_data_tm (Wrap tm) =
  let (Wrap tm) = strip_outer_parens (Wrap tm) in
  match tm.value with
  | Notn ((Builtins.Data, _), n) -> (
      let rec go acc = function
        | [ Token (Token.RBracket, _) ] -> Some (List.rev acc)
        | Token (Token.Op "|", _) :: Term constr :: obs -> go (Wrap constr :: acc) obs
        | _ -> None
      in
      match args n with
      | [ Token (Token.Data, _); Token (Token.LBracket, _); Token (Token.RBracket, _) ] -> Some []
      | Token (Token.Data, _) :: Token (Token.LBracket, _) :: obs -> go [] obs
      | _ -> None)
  | _ -> None

let extract_simple_record_tm (Wrap tm) =
  let (Wrap tm) = strip_outer_parens (Wrap tm) in
  match tm.value with
  | Notn ((Builtins.Record, _), n) -> (
      let rec go acc = function
        | [ Token (Token.RParen, _) ] -> Some (List.rev acc)
        | Token (Token.Op ",", _) :: obs -> go acc obs
        | Term { value = Ident ([ fld ], _); _ } :: Token (Token.Colon, _) :: Term ty :: obs ->
            go ((fld, Wrap ty) :: acc) obs
        | _ -> None
      in
      match args n with
      | Token (Token.Sig, _) :: Token (Token.LParen, _) :: obs -> go [] obs
      | _ -> None)
  | _ -> None

let extract_codata_tm (Wrap tm) =
  let (Wrap tm) = strip_outer_parens (Wrap tm) in
  match tm.value with
  | Notn ((Builtins.Codata, _), _) -> Some ()
  | _ -> None

let wrapped_parse_starts_with_token tok wrapped =
  let (Wrap tm) = strip_outer_parens wrapped in
  match tm.value with
  | Notn (_, n) -> (
      match args n with
      | Token (tok', _) :: _ -> tok' = tok
      | _ -> false)
  | _ -> false

let def_is_typeformer ({ tm; _ } : def) =
  Option.is_some (extract_data_tm tm)
  || Option.is_some (extract_simple_record_tm tm)
  || Option.is_some (extract_codata_tm tm)
  || wrapped_parse_starts_with_token Token.Data tm
  || wrapped_parse_starts_with_token Token.Sig tm
  || wrapped_parse_starts_with_token Token.Codata tm

let defs_are_data_decl defs =
  List.for_all
    (fun ({ head; ty; tm; _ } : def) ->
      match (head, ty, extract_data_tm tm) with
      | Head_name _, Some _, Some _ -> true
      | _ -> false)
    defs

let defs_are_record_decl defs =
  List.for_all
    (fun ({ head; ty; tm; _ } : def) ->
      match (head, ty, extract_simple_record_tm tm) with
      | Head_name _, Some _, Some _ -> true
      | _ -> false)
    defs

module Command = struct
  type t =
    | Axiom of {
        wsaxiom : Whitespace.t list;
        nonparam : unit attribute option;
        name : Trie.path;
        loc : Asai.Range.t option;
        wsname : Whitespace.t list;
        parameters : Parameter.t list;
        wscolon : Whitespace.t list;
        ty : wrapped_parse;
      }
    | TypeSig of type_sig
    | Clause of clause
    | Def of def list
    | Data_decl of def list
    | Record_decl of def list
    (* "synth" is almost just like "echo", so we implement them as one command distinguished by an "eval" flag. *)
    | Echo of {
        wsecho : Whitespace.t list;
        number : int option;
        wsin : Whitespace.t list;
        wsnumber : Whitespace.t list;
        tm : wrapped_parse;
        eval : bool;
      }
    | Notation : {
        fixity : ('left, 'tight, 'right) fixity;
        wsnotation : Whitespace.t list;
        wslparen : Whitespace.t list;
        wstight : Whitespace.t list; (* Empty for outfix *)
        wsellipsis : Whitespace.t list; (* Empty for non-associative *)
        loc : Asai.Range.t option;
        wsrparen : Whitespace.t list;
        pattern : ('left, 'right) User.Pattern.t;
        wscoloneq : Whitespace.t list;
        head : [ `Constr of string | `Constant of Trie.path ];
        wshead : Whitespace.t list;
        args : (string * Whitespace.t list) list;
      }
        -> t
    | Fixity_decl : {
        keyword : [ `Infix | `Infixl | `Infixr ];
        wsfixity : Whitespace.t list;
        fixity : ('left, 'tight, 'right) fixity;
        loc : Asai.Range.t option;
        name : Trie.path;
        wstight : Whitespace.t list;
        wsname : Whitespace.t list;
        pattern : ('left, 'right) User.Pattern.t;
        val_vars : string list;
      }
        -> t
    | Module_decl of {
        wsmodule : Whitespace.t list;
        name : Trie.path;
        loc : Asai.Range.t option;
        wsname : Whitespace.t list;
        parameters : Parameter.t list;
        wswhere : Whitespace.t list;
        body : module_body;
      }
    | Module_app of {
        wsmodule : Whitespace.t list;
        name : Trie.path;
        loc : Asai.Range.t option;
        wsname : Whitespace.t list;
        parameters : Parameter.t list;
        wseq : Whitespace.t list;
        source : Trie.path;
        wssource : Whitespace.t list;
        args : (Whitespace.t list * wrapped_parse) list;
        modifiers : module_modifiers;
      }
    | Open_decl of {
        wsopen : Whitespace.t list;
        wsimport : Whitespace.t list option;
        path : Trie.path;
        loc : Asai.Range.t option;
        wspath : Whitespace.t list;
        public_ : Whitespace.t list option;
        modifiers : module_modifiers;
      }
    | Private of { wsprivate : Whitespace.t list; cmd : t }
    | Import of {
        wsimport : Whitespace.t list;
        export : bool;
        origin : [ `File of string | `Path of Trie.path ];
        wsorigin : Whitespace.t list;
        op : (Whitespace.t list * modifier) option;
      }
    | Chdir of { wschdir : Whitespace.t list; dir : string; wsdir : Whitespace.t list }
    | Solve of {
        wssolve : Whitespace.t list;
        number : int;
        wsnumber : Whitespace.t list;
        column : int;
        wscolumn : Whitespace.t list;
        wscoloneq : Whitespace.t list;
        mutable tm : wrapped_parse;
        mutable parenthesized : bool;
      }
    | Split of {
        wssplit : Whitespace.t list;
        number : int;
        wsnumber : Whitespace.t list;
        wscoloneq : Whitespace.t list;
        (* The whitespace is for the commas.  The first one is ignored. *)
        tms : (Whitespace.t list * wrapped_parse) list;
        mutable printed_term : PPrint.document;
      }
    (* Show and Undo don't get reformatted (see pp_command, below), so there's no need to store whitespace in them, but we do it anyway for completeness. *)
    | Show of {
        wsshow : Whitespace.t list;
        what : [ `Hole of Whitespace.t list * int | `Holes ];
        wswhat : Whitespace.t list;
      }
    | Display of {
        wsdisplay : Whitespace.t list;
        wscoloneq : Whitespace.t list;
        what :
          [ `Chars of Whitespace.t list * Display.chars Display.toggle * Whitespace.t list
          | `Function_boundaries of
            Whitespace.t list * Whitespace.t list * Display.show Display.toggle * Whitespace.t list
          | `Type_boundaries of
            Whitespace.t list * Whitespace.t list * Display.show Display.toggle * Whitespace.t list
          ];
      }
    | Pragma of {
        wsopen : Whitespace.t list;
        wsoptions : Whitespace.t list;
        body : (Token.t * Whitespace.t list) list;
        wsclose : Whitespace.t list;
      }
    | Undo of { wsundo : Whitespace.t list; count : int; wscount : Whitespace.t list }
    | Section of {
        wssection : Whitespace.t list;
        prefix : string list;
        wsprefix : Whitespace.t list;
        wscoloneq : Whitespace.t list;
      }
    | Fmt of {
        wsfmt : Whitespace.t list;
        instant : Instant.t;
        wsinstant : Whitespace.t list;
        wscoloneq : Whitespace.t list;
        cmd : t;
      }
    | End of { wsend : Whitespace.t list }
    | Quit of Whitespace.t list
    | Bof of Whitespace.t list
    | Eof
  and module_body = {
    wslbrace : Whitespace.t list;
    first : t;
    rest : (Whitespace.t list * t) list;
    wsrbrace : Whitespace.t list;
  }
end

include Command

module Parse = struct
  open Parse
  module C = Combinators (Command)
  open C.Basic

  type parsed_def_head = {
    head : def_head;
    name : Trie.path;
    loc : Asai.Range.t option;
    wshead : Whitespace.t list;
  }

  let token x = step "" (fun state _ (tok, w) -> if tok = x then Some (w, state) else None)

  let hidden_name_of_field head suffix = [ ""; head; String.concat "" suffix ]

  let valid_name = function
    | "" :: rest -> Lexer.valid_ident rest
    | name -> Lexer.valid_ident name

  let higher_field_segment =
    step "" (fun state _ (tok, _) ->
        match tok with
        | Ident [ x ] -> Some (x, state)
        | _ -> None)

  let higher_field_suffix =
    let* _ = token LAngle in
    let* first = higher_field_segment in
    let* rest =
      zero_or_more
        (let* _ = token (Op ",") in
         higher_field_segment)
    in
    let* ws = token RAngle in
    return (first :: rest, ws)

  let ident =
    let* name, w =
      step "" (fun state _ (tok, w) ->
          match tok with
          | Ident name -> Some ((name, w), state)
          | _ -> None)
    in
    match name with
    | [ head ] when not (Lexer.all_digits head) ->
        (let* suffix, ws = higher_field_suffix in
         return (hidden_name_of_field head suffix, ws))
        </> return (name, w)
    | _ -> return (name, w)

  let variable =
    let* loc, (xs, w) =
      located
        (step "" (fun state _ (tok, w) ->
             match tok with
             | Ident xs -> Some ((Some xs, w), state)
             | Underscore -> Some ((None, w), state)
             | _ -> None)) in
    match xs with
    | Some [ x ] when Lexer.valid_var x -> return (Some x, w)
    | None -> return (None, w)
    | Some xs -> fatal ~loc:(Range.convert loc) (Invalid_variable xs)

  let parameter =
    let* wslparen = token LParen in
    let* name, names = one_or_more variable in
    let names = name :: names in
    let* wscolon = token Colon in
    let* ty = C.term [ RParen ] in
    let* wsrparen = token RParen in
    return ({ wslparen; names; wscolon; ty; wsrparen } : Parameter.t)

  let attribute : type a. a StringsMap.t -> a attribute option t =
   fun values ->
    let* hash = optional (token (Op "#")) in
    match hash with
    | None -> return None
    | Some wshash -> (
        let* wslparen = token LParen in
        let* (Wrap tm) = C.term [] in
        let* wsrparen = token RParen in
        let strs, wsattr = strings_of_term tm.value in
        match StringsMap.find_opt strs values with
        | None -> fatal ?loc:tm.loc Unrecognized_attribute
        | Some attr -> return (Some { wshash; wslparen; loc = tm.loc; attr; wsattr; wsrparen }))

  let axiom =
    let* wsaxiom = token Axiom in
    let* nonparam = attribute (StringsMap.of_list [ ([ "nonparametric" ], ()) ]) in
    let* nameloc, (name, wsname) = located ident in
    let loc = Some (Range.convert nameloc) in
    let* parameters = zero_or_more parameter in
    let* wscolon = token Colon in
    let* ty = C.term [] in
    return (Command.Axiom { wsaxiom; nonparam; name; loc; wsname; parameters; wscolon; ty })

  let integer =
    step "" (fun state _ (tok, ws) ->
        match tok with
        | Ident [ num ] -> Option.map (fun n -> ((n, ws), state)) (int_of_string_opt num)
        | _ -> None)

  (* Go back in time for parsing only, to use the notations in scope at a given instant.  The usual origin algebraic effect doesn't mesh well with the continuation-based parser monad, so we have to use the built-in parser state. *)
  let set_instant ?severity past =
    match Origin.current () with
    | Instant now when Instant.(past <= now) -> set (Instant past)
    | _ -> fatal ?severity (Invalid_instant (Origin.to_string (Instant past)))

  let echo =
    let* wsecho, eval =
      (let* wsecho = token Echo in
       return (wsecho, true))
      </> let* wsecho = token Synth in
          return (wsecho, false) in
    let* number, wsin, wsnumber, tm =
      (let* wsin = token In in
       let* number, wsnumber = integer in
       let (Found_hole { instant; _ }) = Global.find_hole number in
       let* () = set_instant instant in
       let* tm = C.term [] in
       return (Some number, wsin, wsnumber, tm))
      </> let* tm = C.term [] in
          return (None, [], [], tm) in
    return (Command.Echo { wsecho; number; wsin; wsnumber; tm; eval })

  let tightness : (Whitespace.t list * No.wrapped option * Whitespace.t list * Whitespace.t list) t
      =
    (let* wslparen = token LParen in
     let* sign =
       (let* minusloc, wsminus = located (token (Op "-")) in
        if not (List.is_empty wsminus) then fatal ~loc:(Range.convert minusloc) Parse_error;
        return Q.neg)
       </> return (fun x -> x) in
     let* tloc, (tight, wstight) = located ident in
     let* wsrparen = token RParen in
     let tight = String.concat "." tight in
     match No.of_rat (sign (Q.of_string tight)) with
     | Some tight -> return (wslparen, Some tight, wstight, wsrparen)
     | None | (exception Invalid_argument _) ->
         fatal ~loc:(Range.convert tloc) (Invalid_tightness tight))
    </> return ([], None, [], [])

  let bare_tightness : (No.wrapped * Whitespace.t list) t =
    let* sign =
      (let* minusloc, wsminus = located (token (Op "-")) in
       if not (List.is_empty wsminus) then fatal ~loc:(Range.convert minusloc) Parse_error;
       return Q.neg)
      </> return (fun x -> x)
    in
    let* tloc, (tight, wstight) = located ident in
    let tight = String.concat "." tight in
    match No.of_rat (sign (Q.of_string tight)) with
    | Some tight -> return (tight, wstight)
    | None | (exception Invalid_argument _) ->
        fatal ~loc:(Range.convert tloc) (Invalid_tightness tight)

  let notation_symbol_token ?loc str =
    match Lexer.single str with
    | Some (Op _ as tok) | Some (Ident [ _ ] as tok) -> tok
    | Some tok
      when Array.mem tok
             [|
               LBracket;
               RBracket;
               LBrace;
               RBrace;
               Arrow;
               Mapsto;
               DblMapsto;
               Colon;
               Coloneq;
               DblColoneq;
               Pluseq;
               Dot;
               Ellipsis;
             |] -> tok
    | _ -> fatal ?loc (Invalid_notation_symbol str)

  let pattern_token =
    step "" (fun state _ (tok, ws) ->
        match tok with
        | String str ->
            Some (`Op (notation_symbol_token str, `Nobreak, ws), state)
        | _ -> None)

  let pattern_var =
    let* loc, (x, ws) = located ident in
    match x with
    (* Currently we hard code a `Break space after each *variable* in a notation. *)
    | [ x ] when Lexer.valid_var x -> return (`Var (x, `Break, ws))
    | _ -> fatal ~loc:(Range.convert loc) (Invalid_variable x)

  let pattern_binder =
    let* _ = token LBracket in
    let* loc, (x, _) = located ident in
    let* ws = token RBracket in
    match x with
    | [ x ] when Lexer.valid_var x -> return (`Binder (x, `Break, ws))
    | _ -> fatal ~loc:(Range.convert loc) (Invalid_variable x)

  let pattern_ellipsis =
    let* ws = token Ellipsis in
    return (`Ellipsis ws)

  (* The function fixity_of_pattern "typechecks" a user notation pattern, verifying all the invariants and producing an element of User.Pattern.t in which those invariants are statically guaranteed.  It also interprets ellipses to produce a fixity: a starting ellipse before a variable means left-associative, an ending ellipse after a variable means right-associative, and any other use of ellipses is an error. *)

  type fixity_and_pattern =
    | Fix_pat :
        ('left, 'tight, 'right) fixity * ('left, 'right) User.Pattern.t
        -> fixity_and_pattern

  let fixity_of_pattern pat tight =
    let rec go : type left right.
        [ `Var of string * space * Whitespace.t list
        | `Binder of string * space * Whitespace.t list
        | `Op of Token.t * space * Whitespace.t list
        | `Ellipsis of Whitespace.t list ]
        Bwd.t ->
        (left, right) User.Pattern.t ->
        right User.Pattern.right_t =
     fun bwd_pat new_pat ->
      match bwd_pat with
      | Emp -> Right new_pat
      | Snoc (bwd_pat, `Var v) -> go bwd_pat (User.Pattern.var v new_pat)
      | Snoc (bwd_pat, `Binder v) -> go bwd_pat (User.Pattern.binder v new_pat)
      | Snoc (bwd_pat, `Op v) -> go bwd_pat (Op (v, new_pat))
      | Snoc (_, `Ellipsis _) -> fatal (Unimplemented "internal ellipses in notation") in
    let opnil (a, _, c) = User.Pattern.Op_nil (a, c) in
    let varnil v (a, _, c) = User.Pattern.Var_nil (v, (a, c)) in
    let bindernil v (a, _, c) = User.Pattern.Binder_nil (v, (a, c)) in
    match pat with
    | [] -> fatal (Invalid_notation_pattern "empty")
    | [ `Ellipsis _ ] -> fatal (Invalid_notation_pattern "has no symbols")
    | `Ellipsis _ :: `Op _ :: _ ->
        fatal (Invalid_notation_pattern "prefix/outfix notation can't be left-associative")
    | `Ellipsis _ :: `Ellipsis _ :: _ -> fatal (Invalid_notation_pattern "too many ellipses")
    | `Op v :: pat -> (
        match Bwd.of_list pat with
        | Emp -> (Fix_pat (Outfix, opnil v), [])
        | Snoc (bwd_pat, `Op w) ->
            if Option.is_some tight then fatal Fixity_mismatch;
            let (Right new_pat) = go bwd_pat (opnil w) in
            (Fix_pat (Outfix, Op (v, new_pat)), [])
        | Snoc (Snoc (bwd_pat, `Op o), `Var w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (varnil o w) in
            (Fix_pat (Prefix tight, Op (v, new_pat)), [])
        | Snoc (Snoc (bwd_pat, `Op o), `Binder w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (bindernil o w) in
            (Fix_pat (Prefix tight, Op (v, new_pat)), [])
        | Snoc (Emp, `Var w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            (Fix_pat (Prefix tight, varnil v w), [])
        | Snoc (Emp, `Binder w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            (Fix_pat (Prefix tight, bindernil v w), [])
        | Snoc (Snoc (_, (`Var _ | `Binder _)), (`Var _ | `Binder _)) ->
            fatal (Invalid_notation_pattern "missing symbol between variables")
        | Snoc (Snoc (_, `Ellipsis _), (`Var _ | `Binder _)) ->
            fatal (Unimplemented "internal ellipses in notation")
        | Snoc (Snoc (Snoc (bwd_pat, `Op o), `Var w), `Ellipsis ws) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (varnil o w) in
            (Fix_pat (Prefixr tight, Op (v, new_pat)), ws)
        | Snoc (Snoc (Snoc (bwd_pat, `Op o), `Binder w), `Ellipsis ws) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (bindernil o w) in
            (Fix_pat (Prefixr tight, Op (v, new_pat)), ws)
        | Snoc (Snoc (_, `Op _), `Ellipsis _) | Snoc (_, `Ellipsis _) ->
            fatal (Invalid_notation_pattern "postfix/outfix notation can't be right-associative"))
    | (`Var _ | `Binder _) as v :: pat -> (
        match Bwd.of_list pat with
        | Emp | Snoc (Emp, `Ellipsis _) -> fatal (Invalid_notation_pattern "has no symbols")
        | Snoc (bwd_pat, `Op w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (opnil w) in
            ( Fix_pat
                (Postfix tight, (match v with `Var v -> User.Pattern.var v new_pat | `Binder v -> User.Pattern.binder v new_pat)),
              [] )
        | Snoc (Snoc (bwd_pat, `Op o), `Var w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (varnil o w) in
            ( Fix_pat
                ( Infix tight,
                  match v with
                  | `Var v -> User.Pattern.var v new_pat
                  | `Binder v -> User.Pattern.binder v new_pat ),
              [] )
        | Snoc (Snoc (bwd_pat, `Op o), `Binder w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (bindernil o w) in
            ( Fix_pat
                ( Infix tight,
                  match v with
                  | `Var v -> User.Pattern.var v new_pat
                  | `Binder v -> User.Pattern.binder v new_pat ),
              [] )
        | Snoc (Snoc (Snoc (bwd_pat, `Op o), `Var w), `Ellipsis ws) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (varnil o w) in
            ( Fix_pat
                ( Infixr tight,
                  match v with
                  | `Var v -> User.Pattern.var v new_pat
                  | `Binder v -> User.Pattern.binder v new_pat ),
              ws )
        | Snoc (Snoc (Snoc (bwd_pat, `Op o), `Binder w), `Ellipsis ws) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (bindernil o w) in
            ( Fix_pat
                ( Infixr tight,
                  match v with
                  | `Var v -> User.Pattern.var v new_pat
                  | `Binder v -> User.Pattern.binder v new_pat ),
              ws )
        | Snoc (Snoc (_, (`Var _ | `Binder _)), (`Var _ | `Binder _))
        | Snoc (Emp, (`Var _ | `Binder _))
        | Snoc (Snoc (Snoc (_, (`Var _ | `Binder _)), (`Var _ | `Binder _)), `Ellipsis _)
        | Snoc (Snoc (Emp, (`Var _ | `Binder _)), `Ellipsis _) ->
            fatal (Invalid_notation_pattern "missing symbol between variables")
        | Snoc (Snoc (_, `Ellipsis _), (`Var _ | `Binder _))
        | Snoc (Snoc (Snoc (_, `Ellipsis _), (`Var _ | `Binder _)), `Ellipsis _) ->
            fatal (Unimplemented "internal ellipses in notation")
        | Snoc (Snoc (_, `Op _), `Ellipsis _) ->
            fatal (Invalid_notation_pattern "postfix/outfix notation can't be right-associative")
        | Snoc (Snoc (_, `Ellipsis _), `Ellipsis _) ->
            fatal (Invalid_notation_pattern "too many ellipses"))
    | `Ellipsis ws :: ((`Var _ | `Binder _) as v) :: pat -> (
        match Bwd.of_list pat with
        | Emp -> fatal (Invalid_notation_pattern "has no symbols")
        | Snoc (bwd_pat, `Op w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (opnil w) in
            ( Fix_pat
                ( Postfixl tight,
                  match v with
                  | `Var v -> User.Pattern.var v new_pat
                  | `Binder v -> User.Pattern.binder v new_pat ),
              ws )
        | Snoc (Snoc (bwd_pat, `Op o), `Var w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (varnil o w) in
            ( Fix_pat
                ( Infixl tight,
                  match v with
                  | `Var v -> User.Pattern.var v new_pat
                  | `Binder v -> User.Pattern.binder v new_pat ),
              ws )
        | Snoc (Snoc (bwd_pat, `Op o), `Binder w) ->
            let (No.Wrap tight) = tight <|> Fixity_mismatch in
            let (Right new_pat) = go bwd_pat (bindernil o w) in
            ( Fix_pat
                ( Infixl tight,
                  match v with
                  | `Var v -> User.Pattern.var v new_pat
                  | `Binder v -> User.Pattern.binder v new_pat ),
              ws )
        | Snoc (Snoc (_, (`Var _ | `Binder _)), (`Var _ | `Binder _))
        | Snoc (Emp, (`Var _ | `Binder _)) ->
            fatal (Invalid_notation_pattern "missing symbol between variables")
        | Snoc (Snoc (_, `Ellipsis _), (`Var _ | `Binder _)) ->
            fatal (Unimplemented "internal ellipses in notation")
        | Snoc (_, `Ellipsis _) ->
            fatal (Invalid_notation_pattern "can't be both right and left associative"))

  type fixity_decl_data =
    | Fixity_decl_data :
        {
          fixity : ('left, 'tight, 'right) fixity;
          pattern : ('left, 'right) User.Pattern.t;
          val_vars : string list;
        }
        -> fixity_decl_data

  let fixity_decl_data_of_name ?loc keyword tight name =
    let bad msg = fatal ?loc (Invalid_notation_pattern msg) in
    let is_empty s = String.length s = 0 in
    let pieces = String.split_on_char '_' name in
    if List.length pieces < 2 then bad "fixity name must contain at least one underscore slot";
    if List.for_all is_empty pieces then
      bad "fixity name must contain at least one non-underscore chunk";
    List.iteri
      (fun i piece ->
        if i > 0 && i < List.length pieces - 1 && is_empty piece then
          bad "adjacent underscores are not allowed in fixity names")
      pieces;
    let left_open =
      match pieces with
      | first :: _ -> is_empty first
      | [] -> fatal (Anomaly "empty fixity name pieces")
    in
    let right_open =
      match List.rev pieces with
      | last :: _ -> is_empty last
      | [] -> fatal (Anomaly "empty fixity name pieces")
    in
    if not left_open && not right_open then
      bad "outfix underscore names must use the notation command";
    let val_vars = List.init (List.length pieces - 1) (fun i -> "arg" ^ string_of_int (i + 1)) in
    let atoms =
      let rec go i = function
        | [] -> []
        | [ piece ] ->
            if is_empty piece then []
            else [ `Op (notation_symbol_token ?loc piece, `Nobreak, []) ]
        | piece :: rest ->
            (if is_empty piece then []
             else [ `Op (notation_symbol_token ?loc piece, `Nobreak, []) ])
            @ [ `Var ("arg" ^ string_of_int i, `Break, []) ]
            @ go (i + 1) rest
      in
      go 1 pieces
    in
    let atoms =
      match (keyword, left_open, right_open) with
      | `Infix, true, true | `Infix, false, true | `Infix, true, false -> atoms
      | `Infixl, true, true | `Infixl, true, false -> `Ellipsis [] :: atoms
      | `Infixr, true, true | `Infixr, false, true -> atoms @ [ `Ellipsis [] ]
      | `Infixl, false, true ->
          bad "infixl requires an infix or postfix underscore name"
      | `Infixr, true, false ->
          bad "infixr requires an infix or prefix underscore name"
      | _, false, false ->
          bad "outfix underscore names must use the notation command"
    in
    match (keyword, atoms) with
    | `Infixr, [ `Op (tok, _, _); `Var (arg, _, _); `Ellipsis [] ]
    | `Infixr, [ `Op (tok, _, _); `Var (arg, _, _) ] ->
        Fixity_decl_data
          { fixity = Prefixr tight; pattern = User.Pattern.Var_nil ((tok, `Nobreak, []), (arg, [])); val_vars }
    | `Infixl, [ `Var (arg, _, _); `Op (tok, _, _) ] ->
        Fixity_decl_data
          {
            fixity = Postfixl tight;
            pattern = User.Pattern.Var ((arg, `Break, []), User.Pattern.Op_nil (tok, []));
            val_vars;
          }
    | _ ->
        let Fix_pat (fixity, pattern), _ = fixity_of_pattern atoms (Some (No.Wrap tight)) in
        Fixity_decl_data { fixity; pattern; val_vars }

  let def_name_of_pattern pattern = [ "«" ^ User.Pattern.to_string pattern ^ "»" ]

  let def_head =
    backtrack
      (let* wslparen, tight, wstight, wsrparen = tightness in
       let* patloc, (wspatlparen, pat, pattern, wshead) =
         located
           (let* wspatlparen = token LParen in
            let* pat, pattern =
              one_or_more (pattern_token </> pattern_binder </> pattern_var </> pattern_ellipsis)
            in
            let* wshead = token RParen in
            return (wspatlparen, pat, pattern, wshead)) in
       let pattern = pat :: pattern in
       let Fix_pat (fixity, pattern), wsellipsis = fixity_of_pattern pattern tight in
       let name = def_name_of_pattern pattern in
       return
         {
           head =
             Head_notation { fixity; wslparen; wstight; wsellipsis; wsrparen; wspatlparen; pattern };
           name;
           loc = Some (Range.convert patloc);
           wshead;
         })
      ""
    </> let* nameloc, (name, wshead) = located ident in
        return { head = Head_name name; name; loc = Some (Range.convert nameloc); wshead }

  let def tok =
    let* wsdef = token tok in
    let* { head; name; loc; wshead } = def_head in
    if not (valid_name name) then fatal ?loc (Invalid_constant_name (name, None));
    let* parameters = zero_or_more parameter in
    let* ty, wscoloneq, tm =
      (let* wscolon = token Colon in
       let* ty = C.term [ Coloneq ] in
       let* wscoloneq = token Coloneq in
       let* tm = C.term [] in
       return (Some (wscolon, ty), wscoloneq, tm))
      </>
      let* wscoloneq = token Coloneq in
      let* tm = C.term [] in
      return (None, wscoloneq, tm) in
    return ({ wsdef; head; name; loc; wshead; parameters; ty; wscoloneq; tm } : def)

  let def_and =
    let* first = def Def in
    let* rest = zero_or_more (def And) in
    return (Command.Def (first :: rest))

  let removed_def =
    let* _ = token Def in
    fatal Def_syntax_removed

  let type_sig_until stops =
    backtrack
      (let* nameloc, (name, wsname) = located ident in
       let loc = Some (Range.convert nameloc) in
       if not (valid_name name) then fatal ?loc (Invalid_constant_name (name, None));
       let* wscolon = token Colon in
       let* ty = C.term stops in
       return (Command.TypeSig { name; loc; wsname; wscolon; ty }))
      ""

  let type_sig = type_sig_until []

  let rec local_cmd () =
    (let* sig_cmd = type_sig_until [ Op ";"; RBrace ] in
     match sig_cmd with
     | Command.TypeSig sig_cmd -> return (Local_type_sig sig_cmd)
     | _ -> fatal (Anomaly "local signature parsed as non-signature command"))
    </> let* clause = clause_until [ Token.Where; Op ";"; RBrace ] in
        return (Local_clause clause)

  and where_block () =
    let* wswhere = token Where in
    let* wslbrace = token LBrace in
    let* first = local_cmd () in
    let* rest =
      zero_or_more
        (let* wssemi = token (Op ";") in
         let* cmd = local_cmd () in
         return (wssemi, cmd))
    in
    let* wsrbrace = token RBrace in
    return { wswhere; wslbrace; first; rest; wsrbrace }

  and clause_until stops =
    let* lhs = C.term [ Op "=" ] in
    let* wseq = token (Op "=") in
    let* tm = C.term stops in
    let* where_block = optional (where_block ()) in
    return { lhs; wseq; tm; where_block }

  let clause =
    let* clause = clause_until [ Token.Where ] in
    return (Command.Clause clause)

  let field_name =
    let* loc, (name, wsname) = located ident in
    match name with
    | [ fld ] when Lexer.valid_field fld && not (Lexer.all_digits fld) -> return (fld, wsname)
    | _ -> fatal ~loc:(Range.convert loc) Parse_error

  let data_decl_clause =
    let* tm = C.term [ Op ";"; RBrace ] in
    return tm

  let data_decl tok =
    let* wsdef = token tok in
    let* nameloc, (name, wshead) = located ident in
    let loc = Some (Range.convert nameloc) in
    if not (valid_name name) then fatal ?loc (Invalid_constant_name (name, None));
    let* parameters = zero_or_more parameter in
    let* wscolon = token Colon in
    let* ty = C.term [ Where ] in
    let* _ = token Where in
    let* _ = token LBrace in
    let* first = optional data_decl_clause in
    let* rest =
      zero_or_more
        (let* _ = token (Op ";") in
         data_decl_clause)
    in
    let* _ = token RBrace in
    let constrs = Option.fold ~none:[] ~some:(fun tm -> tm :: rest) first in
    return
      {
        wsdef;
        head = Head_name name;
        name;
        loc;
        wshead;
        parameters;
        ty = Some (wscolon, ty);
        wscoloneq = [];
        tm = synth_data_tm constrs;
      }

  let data_decl_and =
    let* first = data_decl Data in
    let* rest = zero_or_more (data_decl And) in
    return (Command.Data_decl (first :: rest))

  let record_field_clause =
    (let* _ = token Constructor_kw in
     fatal Unsupported_record_constructor_clause)
    </> let* fld, _wsfld = field_name in
        let* _ = token Colon in
        let* ty = C.term [ Op ";"; RBrace ] in
        return (fld, ty)

  let record_decl tok =
    let* wsdef = token tok in
    let* nameloc, (name, wshead) = located ident in
    let loc = Some (Range.convert nameloc) in
    if not (valid_name name) then fatal ?loc (Invalid_constant_name (name, None));
    let* parameters = zero_or_more parameter in
    let* wscolon = token Colon in
    let* ty = C.term [ Where ] in
    let* _ = token Where in
    let* _ = token LBrace in
    let* fields =
      (let* _ = token RBrace in
       return [])
      </> (let* _ = token Constructor_kw in
           fatal Unsupported_record_constructor_clause)
      </> let* _ = token Field_kw in
          let* first = record_field_clause in
          let* rest =
            zero_or_more
              (let* _ = token (Op ";") in
               record_field_clause)
          in
          let* _ = token RBrace in
          return (first :: rest)
    in
    return
      {
        wsdef;
        head = Head_name name;
        name;
        loc;
        wshead;
        parameters;
        ty = Some (wscolon, ty);
        wscoloneq = [];
        tm = synth_record_tm fields;
      }

  let record_decl_and =
    let* first = record_decl Record in
    let* rest = zero_or_more (record_decl And) in
    return (Command.Record_decl (first :: rest))

  let notation_head =
    (let* name, ws = ident in
     return (`Constant name, ws))
    </> let* ws = token Set in
        return (`Constant [ "Set" ], ws)

  let notation_var =
    let* loc, (x, ws) = located ident in
    match x with
    | [ x ] when Lexer.valid_var x -> return (x, ws)
    | _ -> fatal ~loc:(Range.convert loc) (Invalid_variable x)

  let notation =
    let* wsnotation = token Notation in
    let* wslparen, tight, wstight, wsrparen = tightness in
    let* loc, (pat, pattern) =
      located
        (one_or_more (pattern_token </> pattern_binder </> pattern_var </> pattern_ellipsis))
    in
    let loc = Some (Range.convert loc) in
    let pattern = pat :: pattern in
    let Fix_pat (fixity, pattern), wsellipsis = fixity_of_pattern pattern tight in
    let* wscoloneq = token Coloneq in
    let* head, wshead = notation_head in
    let* args = zero_or_more notation_var in
    return
      (Command.Notation
         {
           fixity;
           wsnotation;
           wstight;
           wslparen;
           wsellipsis;
           loc;
           wsrparen;
           pattern;
           wscoloneq;
           head;
           wshead;
           args;
         })

  let fixity_decl =
    let* keyword, wsfixity =
      (let* wsfixity = token Infix in
       return (`Infix, wsfixity))
      </> (let* wsfixity = token Infixl in
           return (`Infixl, wsfixity))
      </> let* wsfixity = token Infixr in
          return (`Infixr, wsfixity)
    in
    let* (No.Wrap tight), wstight = bare_tightness in
    let* nameloc, (name, wsname) = located ident in
    let loc = Some (Range.convert nameloc) in
    if not (valid_name name) then fatal ?loc (Invalid_constant_name (name, None));
    let final_name =
      match List.rev name with
      | final_name :: _ -> final_name
      | [] -> fatal (Anomaly "empty fixity declaration name")
    in
    let Fixity_decl_data { fixity; pattern; val_vars } =
      fixity_decl_data_of_name ?loc keyword tight final_name
    in
    return (Command.Fixity_decl { keyword; wsfixity; fixity; loc; name; wstight; wsname; pattern; val_vars })

  let path =
    ident
    </> let* wsdot = token Dot in
        return ([], wsdot)

  let module_name_list =
    let* wslparen = token LParen in
    let* item, wsitem = path in
    let* rest =
      zero_or_more
        (let* wssemi = token (Op ";") in
         let* item, wsitem = path in
         return (item, wssemi @ wsitem))
    in
    let* wsrparen = token RParen in
    return { wslparen; items = (item, wsitem) :: rest; wsrparen }

  let to_keyword =
    step "" (fun state _ (tok, ws) ->
        match tok with
        | Ident [ "to" ] -> Some (ws, state)
        | _ -> None)

  let module_renaming_item =
    let* source, wssource = path in
    let* wsto = to_keyword in
    let* target, wstarget = path in
    return { source; wssource; wsto; target; wstarget }

  let module_modifiers =
    let* filter =
      optional
        ((let* wsusing = token Using in
          let* names = module_name_list in
          return (`Using (wsusing, names)))
        </> let* wshiding = token Hiding in
            let* names = module_name_list in
            return (`Hiding (wshiding, names)))
    in
    let* renaming =
      optional
        (let* wsrenaming = token Renaming in
         let* wslparen = token LParen in
         let* first = module_renaming_item in
         let* rest =
           zero_or_more
             (let* _ = token (Op ";") in
              module_renaming_item)
         in
         let* wsrparen = token RParen in
         return (wsrenaming, wslparen, first :: rest, wsrparen))
    in
    return { filter; renaming }

  let rec split_module_app_rhs accum wrapped =
    match strip_outer_parens wrapped with
    | Wrap { value = App { fn; arg; _ }; _ } -> split_module_app_rhs (Wrap arg :: accum) (Wrap fn)
    | head -> (head, accum)

  let module_app_source rhs =
    let head, args = split_module_app_rhs [] rhs in
    match head with
    | Wrap { value = Ident (source, _); loc } ->
        (source, loc, List.map (fun arg -> ([], arg)) args)
    | Wrap { loc; _ } -> fatal ?loc Parse_error

  let removed_module_surface () =
    (let* _ = token Import in
     fatal Parse_error)
    </> (let* _ = token Export in
         fatal Parse_error)
    </> (let* _ = token Section in
         fatal Parse_error)
    </> let* _ = token End in
        fatal Parse_error

  let rec modifier () =
    let* m =
      step "" (fun state _ (tok, ws) ->
          match tok with
          | Ident [ "all" ] -> Some (`All ws, state)
          | Ident [ "id" ] -> Some (`Id ws, state)
          | Ident [ "only" ] -> Some (`Only ws, state)
          | In -> Some (`In ws, state)
          | Ident [ "none" ] -> Some (`None ws, state)
          | Ident [ "except" ] -> Some (`Except ws, state)
          | Ident [ "renaming" ] -> Some (`Renaming ws, state)
          | Ident [ "seq" ] -> Some (`Seq ws, state)
          | Ident [ "union" ] -> Some (`Union ws, state)
          | _ -> None) in
    match m with
    | `All wsall -> return (All { wsall })
    | `Id wsid -> return (Id { wsid })
    | `Only wsonly ->
        let* path, wspath = path in
        return (Only { wsonly; path; wspath })
    | `In wsin ->
        let* path, wspath = path in
        let* op = modifier () in
        return (In { wsin; path; wspath; op })
    | `None wsnone -> return (MNone { wsnone })
    | `Except wsexcept ->
        let* path, wspath = path in
        return (Except { wsexcept; path; wspath })
    | `Renaming wsrenaming ->
        let* source, wssource = path in
        let* target, wstarget = path in
        return (Renaming { wsrenaming; source; wssource; target; wstarget })
    | `Seq wsseq ->
        let* wslparen = token LParen in
        let* ops =
          zero_or_more_fold_left Bwd.Emp
            (fun x y -> return (Snoc (x, y)))
            (backtrack
               (let* op = modifier () in
                let* wssemi = token (Op ",") in
                return (op, wssemi))
               "") in
        let* lastop = optional (modifier ()) in
        let ops =
          Bwd.fold_right
            (fun x y -> x :: y)
            ops
            (Option.fold ~none:[] ~some:(fun x -> [ (x, []) ]) lastop) in
        let* wsrparen = token RParen in
        return (Seq { wsseq; wslparen; ops; wsrparen })
    | `Union wsunion ->
        let* wslparen = token LParen in
        let* ops =
          zero_or_more_fold_left Bwd.Emp
            (fun x y -> return (Snoc (x, y)))
            (backtrack
               (let* op = modifier () in
                let* wssemi = token (Op ",") in
                return (op, wssemi))
               "") in
        let* lastop = optional (modifier ()) in
        let ops =
          Bwd.fold_right
            (fun x y -> x :: y)
            ops
            (Option.fold ~none:[] ~some:(fun x -> [ (x, []) ]) lastop) in
        let* wsrparen = token RParen in
        return (Union { wsunion; wslparen; ops; wsrparen })

  let chdir =
    let* wschdir = token Chdir in
    let* dir, wsdir =
      step "" (fun state _ (tok, ws) ->
          match tok with
          | String dir -> Some ((dir, ws), state)
          | _ -> None) in
    return (Chdir { wschdir; dir; wsdir })

  let solve =
    let* wssolve = token Solve in
    let* number, wsnumber = integer in
    let* column, wscolumn = integer </> return (0, []) in
    let* wscoloneq = token Coloneq in
    let (Found_hole { instant; _ }) = Global.find_hole number in
    let* () = set_instant instant in
    let* tm = C.term [] in
    return
      (Solve { wssolve; number; wsnumber; column; wscolumn; wscoloneq; tm; parenthesized = false })

  let split =
    let* wssplit = token Split in
    let* number, wsnumber = integer in
    let* wscoloneq = token Coloneq in
    let (Found_hole { instant; _ }) = Global.find_hole number in
    let* () = set_instant instant in
    let* tm = C.term [] in
    let* tms =
      zero_or_more
        (let* wscomma = token (Op ",") in
         let* tm = C.term [] in
         return (wscomma, tm)) in
    let tms = ([], tm) :: tms in
    return (Split { wssplit; number; wsnumber; wscoloneq; tms; printed_term = PPrint.empty })

  let show =
    let* wsshow = token Show in
    let* what =
      step "" (fun state _ (tok, ws) ->
          match tok with
          | Ident [ "hole" ] -> Some (`Hole ws, state)
          | Ident [ "holes" ] -> Some (`Holes ws, state)
          | _ -> None) in
    let* what, wswhat =
      match what with
      | `Hole ws ->
          let* number, wsnumber = integer in
          return (`Hole (ws, number), wsnumber)
      | `Holes ws -> return (`Holes, ws) in
    return (Show { wsshow; what; wswhat })

  let chars_of_token : Token.t -> Display.chars Display.toggle option = function
    | Ident [ "unicode" ] -> Some (`Set `Unicode)
    | Ident [ "ascii" ] -> Some (`Set `ASCII)
    | Ident [ "toggle" ] -> Some `Toggle
    | _ -> None

  let show_of_token : Token.t -> Display.show Display.toggle option = function
    | Ident [ "on" ] -> Some (`Set `Show)
    | Ident [ "off" ] -> Some (`Set `Hide)
    | Ident [ "toggle" ] -> Some `Toggle
    | _ -> None

  let display =
    let* wsdisplay = token Display in
    let* what, wswhat =
      step "" (fun state _ (tok, ws) ->
          match tok with
          | Ident [ "chars" ] -> Some ((`Chars, ws), state)
          | Ident [ "function" ] -> Some ((`Function, ws), state)
          | Ident [ "type" ] -> Some ((`Type, ws), state)
          | _ -> None) in
    match what with
    | `Chars ->
        let* wscoloneq = token Coloneq in
        step "" (fun state _ (tok, ws) ->
            let open Monad.Ops (Monad.Maybe) in
            let* chars = chars_of_token tok in
            return (Display { wsdisplay; wscoloneq; what = `Chars (wswhat, chars, ws) }, state))
    | `Function ->
        let* wsb = token (Ident [ "boundaries" ]) in
        let* wscoloneq = token Coloneq in
        step "" (fun state _ (tok, ws) ->
            let open Monad.Ops (Monad.Maybe) in
            let* show = show_of_token tok in
            return
              ( Display { wsdisplay; wscoloneq; what = `Function_boundaries (wswhat, wsb, show, ws) },
                state ))
    | `Type ->
        let* wsb = token (Ident [ "boundaries" ]) in
        let* wscoloneq = token Coloneq in
        step "" (fun state _ (tok, ws) ->
            let open Monad.Ops (Monad.Maybe) in
            let* show = show_of_token tok in
            return
              ( Display { wsdisplay; wscoloneq; what = `Type_boundaries (wswhat, wsb, show, ws) },
                state ))

  let implicit_of_token : Token.t -> [ `Implicit | `Explicit ] option = function
    | Ident [ "implicit" ] -> Some `Implicit
    | Ident [ "explicit" ] -> Some `Explicit
    | _ -> None

  let pragma_body_token =
    step "" (fun state _ (tok, ws) ->
        match tok with
        | PragmaClose | Eof | Bof -> None
        | _ -> Some ((tok, ws), state))

  let pragma =
    let* wsopen = token PragmaOpen in
    let* wsoptions =
      step "" (fun state _ (tok, ws) ->
          match tok with
          | Ident [ "OPTIONS" ] -> Some (ws, state)
          | _ -> None)
    in
    let* body = zero_or_more pragma_body_token in
    let* wsclose = token PragmaClose in
    return (Command.Pragma { wsopen; wsoptions; body; wsclose })

  let undo =
    let* wsundo = token Undo in
    let* count, wscount = integer in
    return (Command.Undo { wsundo; count; wscount })

  let quit =
    let* wsquit = token Quit in
    return (Command.Quit wsquit)

  let bof =
    let* ws = C.bof in
    return (Command.Bof ws)

  let eof =
    let* () = expect_end () in
    return Command.Eof

  let rec fmt () =
    let* wsfmt = token Fmt in
    let* instant, wsinstant = integer in
    let instant = Instant.of_int instant in
    let* wscoloneq = token Coloneq in
    let* () = set_instant ~severity:Error instant in
    let* cmd = command () in
    return (Fmt { wsfmt; instant; wsinstant; wscoloneq; cmd })

  and module_body_command () =
    axiom
    </> removed_def
    </> data_decl_and
    </> record_decl_and
    </> type_sig
    </> clause
    </> echo
    </> notation
    </> fixity_decl
    </> module_decl_or_app ()
    </> open_decl ()
    </> private_cmd ()
    </> removed_module_surface ()
    </> chdir
    </> solve
    </> split
    </> show
    </> display
    </> pragma
    </> undo
    </> fmt ()

  and module_body () =
    let* wslbrace = token LBrace in
    let* first = module_body_command () in
    let* rest =
      zero_or_more
        (let* wssemi = token (Op ";") in
         let* cmd = module_body_command () in
         return (wssemi, cmd))
    in
    let* wsrbrace = token RBrace in
    return { wslbrace; first; rest; wsrbrace }

  and module_decl_or_app () =
    let* wsmodule = token Module in
    let* nameloc, (name, wsname) = located ident in
    let loc = Some (Range.convert nameloc) in
    if not (valid_name name) then fatal ?loc (Invalid_constant_name (name, None));
    let* parameters = zero_or_more parameter in
    (let* wswhere = token Where in
     let* body = module_body () in
     return (Command.Module_decl { wsmodule; name; loc; wsname; parameters; wswhere; body }))
    </> (let* wseq = token (Op "=") in
         let* rhs = C.term [ Using; Hiding; Renaming ] in
         let source, _source_loc, args = module_app_source rhs in
         let* modifiers = module_modifiers in
         return
           (Command.Module_app
              {
                wsmodule;
                name;
                loc;
                wsname;
                parameters;
                wseq;
                source;
                wssource = [];
                args;
                modifiers;
              }))

  and open_decl () =
    let* wsopen = token Open in
    let* wsimport = optional (token Import) in
    let* pathloc, (path, wspath) = located path in
    let loc = Some (Range.convert pathloc) in
    let* public_ = optional (token Public) in
    let* modifiers = module_modifiers in
    return (Command.Open_decl { wsopen; wsimport; path; loc; wspath; public_; modifiers })

  and private_target () =
    axiom
    </> data_decl_and
    </> record_decl_and
    </> type_sig
    </> clause
    </> module_decl_or_app ()

  and private_cmd () =
    let* wsprivate = token Private in
    let* cmd = private_target () in
    return (Command.Private { wsprivate; cmd })

  and command () =
    bof
    </> module_body_command ()
    </> quit
    </> eof

  let command_or_echo () =
    command ()
    </> let* tm = C.term [] in
        return
          (Command.Echo { wsecho = []; number = None; wsin = []; wsnumber = []; tm; eval = true })

  type open_source = Range.Data.t * [ `String of int * string | `File of In_channel.t ]

  let start_parse ?(or_echo = false) source : C.Lex_and_parse.t * open_source =
    let (env : Range.Data.t), run =
      match source with
      | `String src ->
          ( { source = `String src; length = Int64.of_int (String.length src.content) },
            fun p ->
              let n, p = C.Lex_and_parse.run_on_string_at 0 src.content p in
              (`String (n, src.content), p) )
      | `File name -> (
          try
            let ic = In_channel.open_text name in
            ( { source = `File name; length = In_channel.length ic },
              fun p -> (`File ic, C.Lex_and_parse.run_on_channel ic p) )
          with Sys_error _ -> fatal (No_such_file name)) in
    Range.run ~env @@ fun () ->
    let p =
      C.Lex_and_parse.make Lexer.Parser.start
        (C.Basic.make_partial (Origin.current ())
           (if or_echo then command_or_echo () else command ())) in
    let out, p = run p in
    (C.ensure_success p, (env, out))

  let restart_parse ?(or_echo = false) (p : C.Lex_and_parse.t) ((env, source) : open_source) :
      C.Lex_and_parse.t * open_source =
    let run =
      match source with
      | `String (n, content) ->
          fun p ->
            let n, p = C.Lex_and_parse.run_on_string_at n content p in
            (`String (n, content), p)
      | `File ic -> fun p -> (`File ic, C.Lex_and_parse.run_on_channel ic p) in
    Range.run ~env @@ fun () ->
    let p =
      C.Lex_and_parse.make_next p
        (C.Basic.make_partial (Origin.current ())
           (if or_echo then command_or_echo () else command ())) in
    let out, p = run p in
    (C.ensure_success p, (env, out))

  let final p = C.Lex_and_parse.final p
  let has_consumed_end p = C.Lex_and_parse.has_consumed_end p
end

let string_of_public_name name =
  match name with
  | [ ""; fld; suffix ] when Lexer.valid_field fld && not (Lexer.all_digits fld) ->
      fld ^ "⟨" ^ suffix ^ "⟩"
  | _ -> String.concat "." name

let valid_source_name = function
  | "" :: rest -> Lexer.valid_ident rest
  | name -> Lexer.valid_ident name

let parse_single ?title (content : string) : Whitespace.t list * Command.t option =
  let src : source = `String { content; title } in
  let p, src = Parse.start_parse ~or_echo:true src in
  match Parse.final p with
  | Bof ws ->
      let p, src = Parse.restart_parse ~or_echo:true p src in
      let cmd = Parse.final p in
      if cmd <> Eof then
        let p, _ = Parse.restart_parse ~or_echo:true p src in
        let eof = Parse.final p in
        if eof = Eof then (ws, Some cmd) else Core.Reporter.fatal Too_many_commands
      else (ws, None)
  | _ -> Core.Reporter.fatal (Anomaly "interactive parse doesn't start with Bof")

type decomposed_clause_head = {
  name : Trie.path;
  loc : Asai.Range.t option;
  args : wrapped_parse list;
  kind : clause_head_kind;
}

and clause_head_kind =
  | Ordinary_clause
  | Copattern_clause of string * string list

let prenotation_info : User.prenotation -> User.key * User.binder_info option * string list =
  function
  | User { key; binder; val_vars; _ } -> (key, binder, val_vars)

let rec split_app_spine accum (wrapped : wrapped_parse) =
  match strip_outer_parens wrapped with
  | Wrap { value = App { fn; arg; _ }; _ } -> split_app_spine (Wrap arg :: accum) (Wrap fn)
  | head -> (head, accum)

let decompose_copattern_head fld pbij loc outer_args =
  match outer_args with
  | [] -> fatal ?loc Parse_error
  | target :: args -> (
      match strip_outer_parens target with
      | Wrap { value = Ident (name, _); loc = target_loc } ->
          let loc = match target_loc with Some _ -> target_loc | None -> loc in
          { name; loc; args; kind = Copattern_clause (fld, pbij) }
      | Wrap { value = Constr (c, _, _); loc } ->
          fatal ?loc (Invalid_notation_head (Constr.to_string (Constr.intern c)))
      | Wrap { loc; _ } ->
          fatal ?loc
            (Invalid_notation_pattern
               "copattern clauses must start with a field name followed by the defined constant name"))

let decompose_clause_head ?(prefer_ordinary = fun _ -> false) (lhs : wrapped_parse) :
    decomposed_clause_head =
  let head, outer_args = split_app_spine [] lhs in
  match head with
  | Wrap { value = HigherField (fld, pbij, _); loc } ->
      decompose_copattern_head fld (expand_compact_suffix pbij) loc outer_args
  | Wrap { value = Ident ([ fld ], _); loc }
    when Scope.lookup_field [ fld ] <> None
         && not (List.is_empty outer_args)
         && not (prefer_ordinary [ fld ]) ->
      decompose_copattern_head fld [] loc outer_args
  | Wrap { value = Ident (name, _); loc } -> { name; loc; args = outer_args; kind = Ordinary_clause }
  | Wrap { value = Constr (c, _, _); loc } ->
      fatal ?loc (Invalid_notation_head (Constr.to_string (Constr.intern c)))
  | Wrap { value = Notn (notn, d); loc } -> (
      match Scope.lookup_notation (name notn) with
      | Some (user, compiled) ->
          let key, binder, val_vars = prenotation_info user in
          if Option.is_some binder then
            fatal ?loc (Invalid_notation_pattern "binder notations are not available in clause heads");
          let term_args =
            List.filter_map
              (function
                | Term tm -> Some (Wrap tm : wrapped_parse)
                | _ -> None)
              (args d)
          in
          let args_by_pattern =
            try
              List.fold_left2
                (fun acc key tm -> StringsMap.add [ key ] tm acc)
                StringsMap.empty compiled.pat_vars term_args
            with Invalid_argument _ ->
              fatal ?loc (Anomaly "invalid user notation shape in clause head")
          in
          let inner_args =
            List.map
              (fun key ->
                match StringsMap.find_opt [ key ] args_by_pattern with
                | Some arg -> arg
                | None -> fatal ?loc (Anomaly "missing clause-head argument for notation"))
              val_vars
          in
          (match key with
          | `Constant c ->
              { name = Scope.name_of c; loc; args = inner_args @ outer_args; kind = Ordinary_clause }
          | `Constr (c, _) -> fatal ?loc (Invalid_notation_head (Constr.to_string c)))
      | None -> fatal ?loc (Invalid_notation_head (name notn)))
  | Wrap { loc; _ } -> fatal ?loc Parse_error

let ordinary_inner_command : Command.t -> Command.t option = function
  | TypeSig _ as cmd | Clause _ as cmd -> Some cmd
  | Private { cmd = (TypeSig _ as cmd); _ } -> Some cmd
  | Private { cmd = (Clause _ as cmd); _ } -> Some cmd
  | _ -> None

let ordinary_private = function
  | Private { cmd = TypeSig _; _ } | Private { cmd = Clause _; _ } -> true
  | TypeSig _ | Clause _ -> false
  | _ -> false

let ordinary_source_head ?(prefer_ordinary = fun _ -> false) : Command.t -> (Trie.path * Asai.Range.t option) option =
  function
  | TypeSig { name; loc; _ } | Private { cmd = TypeSig { name; loc; _ }; _ } -> Some (name, loc)
  | Clause { lhs; _ } | Private { cmd = Clause { lhs; _ }; _ } ->
      let { name; loc; _ } = decompose_clause_head ~prefer_ordinary lhs in
      Some (name, loc)
  | _ -> None

let predeclare_constant ?loc name =
  if not (valid_source_name name) then fatal ?loc (Invalid_constant_name (name, None));
  Scope.check_name name loc;
  Scope.define ?loc name

let compact_doc doc =
  let buf = Buffer.create 64 in
  PPrint.ToBuffer.compact buf doc;
  Buffer.contents buf

let string_of_term tm = compact_doc (pp_complete_term tm `None)

let parse_generated_term content =
  let p = TermParse.Term.parse (`String { title = Some "generated definition"; content }) in
  TermParse.Term.final p

let rec pi_implicitness_of_type : type a s. (a, s) Term.term -> [ `Implicit | `Explicit ] list =
 fun ty ->
  match ty with
  | Pi (impl, _, _, cods) -> impl :: pi_implicitness_of_type (Term.CodCube.find_top cods)
  | _ -> []

let constructor_data_of_pattern (pattern : wrapped_parse) =
  let head, _ = split_app_spine [] pattern in
  match strip_outer_parens head with
  | Wrap { value = Ident (name, _); _ } -> Option.map snd (Scope.lookup_constr name)
  | Wrap { value = Constr (c, suffix, _); _ } -> Option.map snd (Scope.lookup_constr (c :: suffix))
  | _ -> None

let placeholder_type_of_data_constant const =
  let ty, _ = Global.find const in
  let head = string_of_public_name (Scope.name_of const) in
  let args =
    List.map
      (function
        | `Explicit -> "_"
        | `Implicit -> "{ _ }")
      (pi_implicitness_of_type ty)
  in
  parse_generated_term (String.concat " " (head :: args))

let infer_case_arg_type (patterns : wrapped_parse list) =
  match
    List.fold_left
      (fun acc pat ->
        match constructor_data_of_pattern pat with
        | None -> acc
        | Some const -> Constant.Map.add const () acc)
      Constant.Map.empty patterns
    |> Constant.Map.bindings |> List.map fst
  with
  | [ const ] -> Some (placeholder_type_of_data_constant const)
  | _ -> None

let infer_term_type tm = Option.map placeholder_type_of_data_constant (constructor_data_of_pattern tm)

let ascribe_generated_term tm ty =
  parse_generated_term ("(" ^ string_of_term tm ^ " : " ^ string_of_term ty ^ ")")

let typed_case_args args clauses =
  List.mapi
    (fun i arg ->
      let pats =
        List.filter_map
          (fun (_, ({ args; _ } : decomposed_clause_head)) -> List.nth_opt args i)
          clauses
      in
      match infer_case_arg_type pats with
      | Some ty -> ascribe_generated_term (ident_tm arg) ty
      | None -> ident_tm arg)
    args

let infer_clause_result_type clauses =
  match
    List.fold_left
      (fun acc ({ tm; _ }, _) ->
        match infer_term_type tm with
        | None -> acc
        | Some ty -> string_of_term ty :: acc)
      [] clauses
    |> List.sort_uniq String.compare
  with
  | [ ty ] -> Some (parse_generated_term ty)
  | _ -> None

let infer_local_clause_group_type arity clauses =
  let arg_tys =
    List.init arity (fun i ->
        let pats =
          List.filter_map
            (fun (_, ({ args; _ } : decomposed_clause_head)) -> List.nth_opt args i)
            clauses
        in
        infer_case_arg_type pats)
  in
  let result_ty = infer_clause_result_type clauses in
  if List.for_all Option.is_none arg_tys && Option.is_none result_ty then None
  else
    let parts =
      List.map
        (fun ty -> string_of_term (Option.value ~default:(parse_generated_term "_") ty))
        (arg_tys @ [ result_ty ])
    in
    Some (parse_generated_term (String.concat " → " parts))

let fresh_clause_args arity terms =
  let rec names_of_obs accum = function
    | [] -> accum
    | Token _ :: obs | Ss_token _ :: obs -> names_of_obs accum obs
    | Term tm :: obs -> names_of_tm (names_of_obs accum obs) (Wrap tm)
  and names_of_tm accum (Wrap tm) =
    match tm.value with
    | Ident ([ x ], _) -> StringSet.add x accum
    | Ident (_, _) | Placeholder _ | Hole _ | Constr _ | Field _ | HigherField _ -> accum
    | Superscript (Some tm, _, _) -> names_of_tm accum (Wrap tm)
    | Superscript (None, _, _) -> accum
    | App { fn; arg; _ } -> names_of_tm (names_of_tm accum (Wrap fn)) (Wrap arg)
    | Notn (_, d) -> names_of_obs accum (args d)
  in
  let used = List.fold_left names_of_tm StringSet.empty terms in
  let rec choose i acc =
    if List.length acc = arity then List.rev acc
    else
      let name = "clause_arg" ^ string_of_int i in
      if StringSet.mem name used || List.mem name acc then choose (i + 1) acc
      else choose (i + 1) (name :: acc)
  in
  choose 1 []

let string_of_case_clause args body =
  String.concat ", " (List.map string_of_term args) ^ " → " ^ string_of_term body

let string_of_record_field fld pbij body =
  compact_doc (Print.pp_field fld pbij) ^ " = " ^ string_of_term body

let build_record_term fields =
  let content =
    match fields with
    | [] -> "record { }"
    | _ ->
        "record { "
        ^ String.concat "; "
            (List.map (fun (fld, pbij, tm) -> string_of_record_field fld pbij tm) fields)
        ^ " }"
  in
  parse_generated_term content

let command_of_local_cmd = function
  | Local_type_sig sig_cmd -> Command.TypeSig sig_cmd
  | Local_clause clause -> Command.Clause clause

let cmds_of_where_block ({ first; rest; _ } : where_block) =
  command_of_local_cmd first :: List.map (fun (_, cmd) -> command_of_local_cmd cmd) rest

let string_of_local_name ?loc = function
  | [ name ] -> name
  | name ->
      fatal ?loc
        (Invalid_notation_pattern
           ("local definitions in where-blocks must use unqualified names, not " ^ String.concat "." name))

let build_local_letrec_term defs body =
  let binding_of_def ({ name; loc; ty; tm; _ } : def) =
    let name = string_of_local_name ?loc name in
    let ty = Option.fold ~none:"_" ~some:(fun (_, ty) -> string_of_term ty) ty in
    name ^ " : " ^ ty ^ " = " ^ string_of_term tm
  in
  let body = string_of_term body in
  parse_generated_term
    ("let rec " ^ String.concat " and " (List.map binding_of_def defs) ^ " in " ^ body)

type clause_binder = string option * [ `Explicit | `Implicit ]

let simple_clause_binder arg =
  match strip_outer_parens arg with
  | Wrap { value = Ident ([ x ], _); _ } -> Some (Some x, `Explicit)
  | Wrap { value = Placeholder _; _ } -> Some (None, `Explicit)
  | Wrap { value = Notn ((Postprocess.Braces, _), n); _ } -> (
      match args n with
      | [ Token (LBrace, _); Term { value = Ident ([ x ], _); _ }; Token (RBrace, _) ] ->
          Some (Some x, `Implicit)
      | [ Token (LBrace, _); Term { value = Placeholder _; _ }; Token (RBrace, _) ] ->
          Some (None, `Implicit)
      | _ -> None)
  | _ -> None

let wrap_abs binders tm =
  let vars =
    unparse_abs
      (List.fold_left
         (fun (xs : clause_binder Bwd.t) binder -> Snoc (xs, binder))
         Emp binders)
      { strictness = No.Nonstrict; endpoint = No.minus_omega }
      (No.minusomega_le No.plus_omega) No.minusomega_lt_plusomega
  in
  let (Wrap body) = tm in
  let loc = Range.merge_opt vars.loc body.loc in
  Wrap
    (locate_opt loc
       (prefix ~notn:Builtins.abs
          ~inner:
            (Multiple
               (Left (Token.Lambda, ([], None)), Emp <: Term vars, Left (Token.Arrow, ([], None))))
          ~last:(parenthesize body) ~right_ok:(No.le_refl No.minus_omega)))

let lower_case_only_body args clauses =
  match clauses with
  | [ ({ tm; _ }, ({ args = []; _ } : decomposed_clause_head)) ] when List.is_empty args -> tm
  | _ ->
      let discrs = String.concat ", " (List.map string_of_term (typed_case_args args clauses)) in
      let branches =
        String.concat "; "
          (List.map (fun ({ tm; _ }, ({ args; _ } : decomposed_clause_head)) -> string_of_case_clause args tm) clauses)
      in
      parse_generated_term ("case " ^ discrs ^ " of λ { " ^ branches ^ " }")

let lower_clause_body args clauses =
  match clauses with
  | [ ({ tm; _ }, ({ args = []; _ } : decomposed_clause_head)) ] when List.is_empty args -> tm
  | [ ({ tm; _ }, ({ args = pats; _ } : decomposed_clause_head)) ] -> (
      match List.map simple_clause_binder pats with
      | binders when List.for_all Option.is_some binders ->
          let binders = List.map Option.get binders in
          wrap_abs binders tm
      | _ -> wrap_abs (List.map (fun x -> (Some x, `Explicit)) args) (lower_case_only_body args clauses))
  | _ -> wrap_abs (List.map (fun x -> (Some x, `Explicit)) args) (lower_case_only_body args clauses)

let lower_copattern_body args clauses =
  let fields, clause_args =
    List.fold_left
      (fun (fields, clause_args) ({ tm; _ }, ({ args = pats; kind; loc = _; _ } : decomposed_clause_head)) ->
        match kind with
        | Ordinary_clause -> fatal (Anomaly "ordinary clause in copattern lowering")
        | Copattern_clause (fld, pbij) ->
            let clause_args =
              match clause_args with
              | None -> Some pats
              | Some prev ->
                  if List.map string_of_term prev <> List.map string_of_term pats then
                    fatal
                      (Invalid_notation_pattern
                         "all copattern clauses for one definition must use the same patterns");
                  Some prev
            in
            if List.exists (fun (fld', pbij', _) -> fld = fld' && pbij = pbij') fields then (
              let (Wrap tm) = tm in
              fatal ?loc:tm.loc (Duplicate_method_in_comatch (fld, pbij)));
            (fields @ [ (fld, pbij, tm) ], clause_args))
      ([], None) clauses
  in
  let clause_args = Option.value ~default:[] clause_args in
  let record_tm = build_record_term fields in
  match clause_args with
  | [] -> record_tm
  | pats -> (
      match List.map simple_clause_binder pats with
      | binders when List.for_all Option.is_some binders ->
          let binders = List.map Option.get binders in
          wrap_abs binders record_tm
      | _ ->
          let discrs = String.concat ", " (List.map string_of_term (typed_case_args args clauses)) in
          let branch = String.concat ", " (List.map string_of_term pats) ^ " → " ^ string_of_term record_tm in
          wrap_abs (List.map (fun x -> (Some x, `Explicit)) args)
            (parse_generated_term ("case " ^ discrs ^ " of λ { " ^ branch ^ " }")))

type grouped_definition = {
  signature : type_sig option;
  clauses : (clause * decomposed_clause_head) list;
}

let rec lower_clause_rhs ({ tm; where_block; _ } : clause) =
  match where_block with
  | None -> tm
  | Some block ->
      let defs = defs_of_pending_commands ~infer_missing_tys:true (cmds_of_where_block block) in
      build_local_letrec_term defs tm

and defs_of_pending_commands ?(infer_missing_tys = false) cmds =
  let signature_names =
    List.fold_left
      (fun names -> function
        | cmd -> (
            match ordinary_inner_command cmd with
            | Some (TypeSig { name; _ }) -> StringsMap.add name () names
            | _ -> names))
      StringsMap.empty cmds
  in
  let prefer_ordinary grouped name =
    StringsMap.mem name signature_names || StringsMap.mem name grouped
  in
  let add_first_seen name order =
    if List.exists (( = ) name) order then order else order @ [ name ]
  in
  let grouped, order =
    List.fold_left
      (fun (grouped, order) cmd ->
        match ordinary_inner_command cmd with
        | Some (TypeSig sig_cmd) ->
            let entry =
              match StringsMap.find_opt sig_cmd.name grouped with
              | Some entry ->
                  if Option.is_some entry.signature then
                    fatal ?loc:sig_cmd.loc (Invalid_notation_pattern "duplicate type signature in definition group");
                  { entry with signature = Some sig_cmd }
              | None -> { signature = Some sig_cmd; clauses = [] }
            in
            (StringsMap.add sig_cmd.name entry grouped, add_first_seen sig_cmd.name order)
        | Some (Clause clause) ->
            let head = decompose_clause_head ~prefer_ordinary:(prefer_ordinary grouped) clause.lhs in
            let entry =
              match StringsMap.find_opt head.name grouped with
              | Some entry -> { entry with clauses = entry.clauses @ [ (clause, head) ] }
              | None -> { signature = None; clauses = [ (clause, head) ] }
            in
            (StringsMap.add head.name entry grouped, add_first_seen head.name order)
        | _ -> (grouped, order))
      (StringsMap.empty, []) cmds
  in
  List.map
    (fun name ->
      let { signature; clauses } = StringsMap.find name grouped in
      match clauses with
      | [] ->
          let loc = Option.bind signature (fun sig_cmd -> sig_cmd.loc) in
          fatal ?loc (Invalid_notation_pattern "type signature must be followed by at least one clause")
      | (_, first_head) :: rest ->
          let arity = List.length first_head.args in
          List.iter
            (fun (_, ({ args; loc; kind; _ } : decomposed_clause_head)) ->
              if List.length args <> arity then
                fatal ?loc (Invalid_notation_pattern "all clauses for one definition must have the same arity");
              match (first_head.kind, kind) with
              | Ordinary_clause, Ordinary_clause -> ()
              | Copattern_clause _, Copattern_clause _ -> ()
              | _ ->
                  fatal ?loc
                    (Invalid_notation_pattern
                       "ordinary clauses and copattern clauses cannot be mixed in one definition"))
            rest;
          (match first_head.kind with
          | Ordinary_clause ->
              if arity = 0 && List.length clauses > 1 then
                fatal ?loc:first_head.loc
                  (Invalid_notation_pattern "a nullary definition may not have more than one clause")
          | Copattern_clause _ -> ());
          let loc =
            match signature with
            | Some sig_cmd -> sig_cmd.loc
            | None -> first_head.loc
          in
          let clauses =
            List.map (fun ((clause : clause), head) -> ({ clause with tm = lower_clause_rhs clause; where_block = None }, head)) clauses
          in
          let inferred_ty =
            match (infer_missing_tys, signature, first_head.kind) with
            | true, None, Ordinary_clause -> infer_local_clause_group_type arity clauses
            | _ -> None
          in
          let used_terms =
            List.concat_map
              (fun ({ tm; _ }, ({ args; _ } : decomposed_clause_head)) -> tm :: args)
              clauses
          in
          let clause_args = fresh_clause_args arity used_terms in
          {
            wsdef = [];
            head = Head_name name;
            name;
            loc;
            wshead = [];
            parameters = [];
            ty =
              (match signature with
              | Some sig_cmd -> Some (sig_cmd.wscolon, sig_cmd.ty)
              | None -> Option.map (fun ty -> ([], ty)) inferred_ty);
            wscoloneq = [];
            tm =
              (match first_head.kind with
              | Ordinary_clause -> lower_clause_body clause_args clauses
              | Copattern_clause _ -> lower_copattern_body clause_args clauses);
          })
    order

let pending_commands_are_complete cmds =
  let signature_names =
    List.fold_left
      (fun names -> function
        | cmd -> (
            match ordinary_inner_command cmd with
            | Some (TypeSig { name; _ }) -> StringsMap.add name () names
            | _ -> names))
      StringsMap.empty cmds
  in
  let signatures, clauses =
    List.fold_left
      (fun (signatures, clauses) cmd ->
        match ordinary_inner_command cmd with
        | Some (TypeSig { name; _ }) -> (StringsMap.add name () signatures, clauses)
        | Some (Clause { lhs; _ }) ->
            let { name; _ } =
              decompose_clause_head ~prefer_ordinary:(fun name -> StringsMap.mem name signature_names) lhs
            in
            (signatures, StringsMap.add name () clauses)
        | _ -> (signatures, clauses))
      (StringsMap.empty, StringsMap.empty) cmds
  in
  StringsMap.for_all (fun name () -> StringsMap.mem name clauses) signatures

let rec term_mentions_name target (Wrap { value; _ } : wrapped_parse) =
  match value with
  | Ident (name, _) -> name = target
  | HigherField (fld, _, _) | Field (fld, _, _) | Constr (fld, _, _) -> target = [ fld ]
  | Placeholder _ | Hole _ -> false
  | App { fn; arg; _ } -> term_mentions_name target (Wrap fn) || term_mentions_name target (Wrap arg)
  | Superscript (Some tm, _, _) -> term_mentions_name target (Wrap tm)
  | Superscript (None, _, _) -> false
  | Notn (n, d) ->
      let via_notation_head =
        match Scope.lookup_notation (name n) with
        | Some (User { key = `Constant c; _ }, _) -> Scope.name_of c = target
        | Some (User { key = `Constr (c, _); _ }, _) -> target = [ Constr.to_string c ]
        | None -> false
      in
      via_notation_head
      ||
      match name n with
      | "data" -> data_obs_mentions_name target (args d)
      | "record" | "codata" -> field_obs_mentions_name target (args d)
      | _ -> obs_mentions_name target (args d)

and obs_mentions_name target = function
  | [] -> false
  | Token _ :: obs | Ss_token _ :: obs -> obs_mentions_name target obs
  | Term tm :: obs -> term_mentions_name target (Wrap tm) || obs_mentions_name target obs

and mentions_in_decl_headless_term target tm =
  let head, spine_args = split_app_spine [] tm in
  match head with
  | Wrap { value = Ident _ | Constr _ | Field _ | HigherField _; _ } ->
      List.exists (term_mentions_name target) spine_args
  | Wrap { value = Notn (n, d); _ } when name n = "ascription" -> (
      match args d with
      | Term tel :: _ :: Term ty :: _ ->
          mentions_in_decl_headless_term target (Wrap tel) || term_mentions_name target (Wrap ty)
      | _ -> obs_mentions_name target (args d))
  | _ -> term_mentions_name target tm

and data_obs_mentions_name target = function
  | [ Token (RBracket, _) ] -> false
  | Token (Op "|", _) :: Term tel :: obs ->
      mentions_in_decl_headless_term target (Wrap tel) || data_obs_mentions_name target obs
  | Term tel :: obs -> mentions_in_decl_headless_term target (Wrap tel) || data_obs_mentions_name target obs
  | Token _ :: obs | Ss_token _ :: obs -> data_obs_mentions_name target obs
  | [] -> false

and field_obs_mentions_name target = function
  | [ Token (RBracket, _) ] | [ Token (RParen, _) ] -> false
  | Token (Op "|", _) :: Term tm :: Token (Colon, _) :: Term ty :: obs ->
      mentions_in_decl_headless_term target (Wrap tm)
      || term_mentions_name target (Wrap ty)
      || field_obs_mentions_name target obs
  | Term tm :: Token (Colon, _) :: Term ty :: obs ->
      mentions_in_decl_headless_term target (Wrap tm)
      || term_mentions_name target (Wrap ty)
      || field_obs_mentions_name target obs
  | Token (Op ",", _) :: obs -> field_obs_mentions_name target obs
  | _ -> false

let rec local_cmd_mentions_name target = function
  | Local_type_sig { ty; _ } -> term_mentions_name target ty
  | Local_clause clause -> clause_mentions_name target clause

and clause_mentions_name target ({ tm; where_block; _ } : clause) =
  term_mentions_name target tm
  ||
  match where_block with
  | None -> false
  | Some { first; rest; _ } ->
      local_cmd_mentions_name target first
      || List.exists (fun (_, cmd) -> local_cmd_mentions_name target cmd) rest

let pending_commands_reference_name cmds target =
  List.exists
    (fun cmd ->
      match ordinary_inner_command cmd with
      | Some (TypeSig { ty; _ }) -> term_mentions_name target ty
      | Some (Clause clause) -> clause_mentions_name target clause
      | _ -> false)
    cmds

let show_hole = function
  | Global.Found_hole { instant; meta; termctx; ty; vars; _ } ->
      emit (Hole (Meta.name meta, PHole (Instant instant, vars, termctx, ty)))

let notation_name pattern = "«" ^ User.Pattern.to_string pattern ^ "»"

let binder_info_of_pattern : type left tight right.
    (left, tight, right) fixity -> (left, right) User.Pattern.t -> User.binder_info option =
 fun fixity pattern ->
  let atoms = User.Pattern.atoms pattern in
  let has_binder =
    List.exists
      (function
        | `Binder _ -> true
        | _ -> false)
      atoms
  in
  let malformed () =
    fatal
      (Invalid_notation_pattern
         "binder notations must be prefix patterns with one or more bracketed slots of the form \
          \"op\" [x] \":\" A \",\" ... B")
  in
  let rec take_ops accum = function
    | `Op tok :: atoms -> take_ops (tok :: accum) atoms
    | atoms -> (List.rev accum, atoms)
  in
  let rec parse_slots prefix_tokens atoms accum =
    match atoms with
    | `Binder binder_name :: `Op Token.Colon :: `Var dom_var :: atoms ->
        let next_tokens, atoms = take_ops [] atoms in
        if List.is_empty next_tokens then malformed ();
        let slot = User.{ prefix_tokens; binder_var = binder_name; dom_var } in
        (match atoms with
        | [ `Var body_var ] ->
            Some User.{ slots = List.rev (slot :: accum); body_prefix_tokens = next_tokens; body_var }
        | `Binder _ :: _ -> parse_slots next_tokens atoms (slot :: accum)
        | _ -> malformed ())
    | _ -> malformed ()
  in
  match atoms with
  | _ :: _ when has_binder -> (
      match fixity with
      | Prefix _ ->
          let prefix_tokens, atoms = take_ops [] atoms in
          if List.is_empty prefix_tokens then malformed ();
          parse_slots prefix_tokens atoms []
      | _ -> fatal (Invalid_notation_pattern "binder notations must be prefix patterns"))
  | _ -> None

let check_pattern_vars_unique : type left right. (left, right) User.Pattern.t -> unit =
 fun pattern ->
  let rec go : type left right. string list -> (left, right) User.Pattern.t -> unit =
   fun seen pattern ->
    match pattern with
    | User.Pattern.Op_nil _ -> ()
    | User.Pattern.Var_nil (_, (x, _)) ->
        if List.mem x seen then fatal (Duplicate_notation_variable x)
    | User.Pattern.Binder_nil (_, (x, _)) ->
        if List.mem x seen then fatal (Duplicate_notation_variable x)
    | User.Pattern.Op (_, pattern) -> go seen pattern
    | User.Pattern.Var ((x, _, _), pattern) ->
        if List.mem x seen then fatal (Duplicate_notation_variable x);
        go (x :: seen) pattern
    | User.Pattern.Binder ((x, _, _), pattern) ->
        if List.mem x seen then fatal (Duplicate_notation_variable x);
        go (x :: seen) pattern in
  go [] pattern

let check_notation_args : type left right.
    (string * Whitespace.t list) list -> (left, right) User.Pattern.t -> unit =
 fun args pattern ->
  check_pattern_vars_unique pattern;
  let rec go : type left right.
      (string * Whitespace.t list) list ->
      (left, right) User.Pattern.t ->
      (string * Whitespace.t list) list =
   fun args pattern ->
    let check_var x =
      let found, rest = List.partition (fun (y, _) -> x = y) args in
      match found with
      | [ _ ] -> rest
      | [] -> fatal (Unused_notation_variable x)
      | _ -> fatal (Notation_variable_used_twice x) in
    match pattern with
    | User.Pattern.Var ((x, _, _), pattern) -> go (check_var x) pattern
    | User.Pattern.Binder (_, pattern) -> go args pattern
    | User.Pattern.Op (_, pattern) -> go args pattern
    | User.Pattern.Op_nil _ -> args
    | User.Pattern.Var_nil (_, (x, _)) -> check_var x
    | User.Pattern.Binder_nil _ -> args in
  match go args pattern with
  | [] -> ()
  | _ :: _ as unbound -> fatal (Unbound_variable_in_notation (List.map fst unbound))

let register_notation : type left tight right.
    loc:Asai.Range.t option ->
    name:string ->
    fixity:(left, tight, right) fixity ->
    pattern:(left, right) User.Pattern.t ->
    key:User.key ->
    val_vars:string list ->
    unit =
 fun ~loc ~name ~fixity ~pattern ~key ~val_vars ->
  let notation_name = [ "notations"; name ] in
  Scope.check_name notation_name loc;
  let binder = binder_info_of_pattern fixity pattern in
  (match (binder, key) with
  | Some _, `Constr (c, _) ->
      fatal (Invalid_notation_head (Constr.to_string c))
  | _ -> ());
  let user = User { name; fixity; pattern; key; binder; val_vars } in
  let shadow = Scope.define_notation user ?loc notation_name in
  List.iter
    (fun key ->
      let keyname =
        match key with
        | `Constr (c, _) -> Constr.to_string c
        | `Constant c -> string_of_public_name (Scope.name_of c) in
      emit (Head_already_has_notation keyname))
    shadow;
  emit (Notation_defined name)

type any_dataconstrs =
  | Dataconstrs : (Constr.t, ('a, 'i) Term.dataconstr) Abwd.t -> any_dataconstrs

type any_codatafields =
  | Codatafields : ('a * 'n * 'et) Term.CodatafieldAbwd.t -> any_codatafields

let register_constructor_names ?loc name const constrs =
  List.iter
    (fun (_, constr) ->
      let cname = Constr.to_string constr in
      Scope.define_constr ?loc [ cname ] constr const;
      Scope.define_constr ?loc (name @ [ cname ]) constr const)
    (List.sort_uniq compare constrs)

let register_data_constructors ?loc name const =
  let rec find_constrs : type n s. (n, s) Term.term -> any_dataconstrs option = function
    | Canonical (Data { constrs; _ }) -> Some (Dataconstrs constrs)
    | Lam (_, _, tm) -> find_constrs tm
    | Realize tm -> find_constrs tm
    | _ -> None
  in
  match Global.find const with
  | _, (`Defined tm, _) -> (
      match find_constrs tm with
      | Some (Dataconstrs constrs) ->
          let rec go :
              type a i.
              (string list * Constr.t) list -> (Constr.t, (a, i) Term.dataconstr) Abwd.t -> _ =
           fun acc -> function
            | Emp -> acc
            | Snoc (constrs, (constr, _)) -> go (([ Constr.to_string constr ], constr) :: acc) constrs
          in
          register_constructor_names ?loc name const (go [] constrs)
      | None -> ())
  | _ -> ()

let register_field_names ?loc name const fields =
  List.iter
    (fun fld ->
      Scope.define_field ?loc [ fld ] fld const;
      Scope.define_field ?loc (name @ [ fld ]) fld const)
    (List.sort_uniq compare fields)

let register_data_fields ?loc name const =
  let rec find_fields : type n s. (n, s) Term.term -> any_codatafields option = function
    | Canonical (Codata { fields; _ }) -> Some (Codatafields fields)
    | Lam (_, _, tm) -> find_fields tm
    | Realize tm -> find_fields tm
    | _ -> None
  in
  match Global.find const with
  | _, (`Defined tm, _) -> (
      match find_fields tm with
      | Some (Codatafields fields) ->
          let rec go : type a n et. string list -> (a * n * et) Term.CodatafieldAbwd.t -> _ =
           fun acc -> function
            | Emp -> acc
            | Snoc (fields, Term.CodatafieldAbwd.Entry (fld, _)) ->
                go (Field.to_string fld :: acc) fields
          in
          register_field_names ?loc name const (go [] fields)
      | None -> ())
  | _ -> ()

let register_syntax_constructors ?loc name const tm =
  register_constructor_names ?loc name const (Builtins.local_constructors_of_term tm)

let register_syntax_fields ?loc name const tm =
  register_field_names ?loc name const (Builtins.local_fields_of_term tm)

let predeclare_ordinary_syntax cmd existing =
  match ordinary_inner_command cmd with
  | Some (Clause { lhs; tm; _ }) -> (
      let { name; loc; _ } = decompose_clause_head lhs in
      match StringsMap.find_opt name existing with
      | Some const ->
          register_syntax_constructors ?loc name const tm;
          register_syntax_fields ?loc name const tm
      | None -> ())
  | _ -> ()

let token_of_fixity_keyword = function
  | `Infix -> Token.Infix
  | `Infixl -> Token.Infixl
  | `Infixr -> Token.Infixr

let to_string : Command.t -> string = function
  | Axiom _ -> "postulate"
  | TypeSig _ -> "signature"
  | Clause _ -> "clause"
  | Def _ -> "def"
  | Data_decl _ -> "data"
  | Record_decl _ -> "record"
  | Echo { eval = true; _ } -> "echo"
  | Echo { eval = false; _ } -> "synth"
  | Notation _ -> "notation"
  | Fixity_decl { keyword; _ } -> Token.to_string (token_of_fixity_keyword keyword)
  | Module_decl _ | Module_app _ -> "module"
  | Open_decl _ -> "open"
  | Private _ -> "private"
  | Import _ -> "import"
  | Chdir _ -> "chdir"
  | Solve _ -> "solve"
  | Split _ -> "split"
  | Show _ -> "show"
  | Display _ -> "display"
  | Pragma _ -> "pragma"
  | Quit _ -> "quit"
  | Undo _ -> "undo"
  | Section _ -> "section"
  | Fmt _ -> "fmt"
  | End _ -> "end"
  | Bof _ -> "bof"
  | Eof -> "eof"

(* Whether a command requires an interactive mode (i.e. not interactive mode and not ProofGeneral interaction). *)
let needs_interactive : Command.t -> bool = function
  | Solve _ | Split _ | Show _ | Undo _ -> true
  | _ -> false

let condense : Command.t -> [ `Import | `Pragma | `None | `Bof ] = function
  | Open_decl _ -> `Import
  | Private { cmd; _ } -> condense cmd
  | Import _ -> `Import
  | Pragma _ -> `Pragma
  | _ -> `None

let tok t : observation = Token (t, ([], None))

(* Subroutine for "split" that generates the cases in a multiple match. *)
let split_match_cases : type a b.
    (a, b) Ctx.t ->
    (string option, a) Bwv.t ->
    (Whitespace.t list * wrapped_parse) list ->
    observation list list =
 fun ctx vars tms ->
  let module S = Monad.State (Bool) in
  let module LS = Monad.ListT (S) in
  let open Monad.Ops (LS) in
  let rec do_args : type a p ap.
      (a, p, ap) Term.Telescope.t ->
      (No.plus_omega, No.strict, No.plus_omega, No.nonstrict) parse located list =
   fun args ->
    match args with
    | Emp -> []
    | Ext (None, _, args) -> locate_opt None (Placeholder []) :: do_args args
    | Ext (Some x, _, args) -> locate_opt None (Ident ([ x ], [])) :: do_args args in
  let rec go = function
    | [] ->
        let* higher = LS.lift S.get in
        let mapsto = if higher then Token.DblMapsto else Mapsto in
        let li, ri = (No.Interval.entire, No.Interval.entire) in
        let h = Hole { li; ri; num = ref 0; ws = []; contents = None } in
        return [ tok mapsto; Term (locate_opt None h) ]
    | (_, Wrap tm) :: tms -> (
        match process vars tm with
        | { value = Synth rtm; loc } -> (
            let _, sty = Check.synth (Kinetic `Nolet) ctx (locate_opt loc rtm) in
            match View.view_type sty "split" with
            | Canonical (_, Data { dim; constrs; _ }, _, _) ->
                let* () =
                  match D.compare_zero dim with
                  | Zero -> return ()
                  | Pos _ -> LS.lift (S.put true) in
                let* c, dc = S.return (Bwd.to_list constrs) in
                let left_ok = No.le_refl No.plus_omega in
                let right_ok = No.le_refl No.plus_omega in
                let first =
                  match dc with
                  | Dataconstr { args; _ } ->
                      Term
                        (List.fold_left
                           (fun fn arg -> locate_opt None (App { fn; arg; left_ok; right_ok }))
                           (locate_opt None (Ident ([ Constr.to_string c ], [])))
                           (do_args args))
                  | Higher_dataconstr _ -> fatal (Invalid_split (`Term, "higher inductive types"))
                in
                let* rest = go tms in
                if List.length rest = 2 then return (first :: rest)
                else return (first :: tok (Op ",") :: rest)
            | _ -> fatal (Invalid_split (`Term, "non-datatype")))
        | _ -> fatal (Nonsynthesizing "splitting term")) in
  fst (go tms false)

let exec_defs_with runner ?(existing = StringsMap.empty) (defs : def list) =
  runner ~holes_allowed:(Ok ()) @@ fun () ->
  let local_constrs =
    List.concat_map
      (fun ({ tm = Wrap tm; _ } : def) -> Builtins.local_constructors_of_term (Wrap tm))
      defs in
  let cdefs, notations =
    List.fold_right
      (fun (({ head; name; loc; parameters; ty; tm = Wrap tm; _ } as def) : def) (cdefs, notations) ->
        (match name with
        | [ str ] ->
            if Option.is_some (deg_of_name str) then
              fatal (Invalid_constant_name (name, Some "that's a degeneracy name"))
        | _ -> ());
        let const =
          lazy
            (match StringsMap.find_opt name existing with
            | Some c -> c
            | None ->
                Scope.check_name name loc;
                Scope.define ?loc name)
        in
        let cdef =
          ( const,
            lazy
              (let (Processed_tel (params, ctx, _)) =
                 Scope.with_local_constrs local_constrs (fun () -> process_tel Emp parameters)
               in
               match ty with
               | Some (_, Wrap ty) ->
                   let ty =
                     Scope.with_local_constrs local_constrs (fun () -> process ctx ty)
                   in
                   let tm =
                     lazy
                       (Scope.with_local_constrs local_constrs (fun () -> process ctx tm))
                   in
                   Core.Command.Def_check { params; ty; tm }
               | None -> (
                   match Scope.with_local_constrs local_constrs (fun () -> process ctx tm) with
                   | { value = Synth tm; loc } ->
                       Def_synth { params; tm = { value = tm; loc } }
                   | _ -> fatal (Nonsynthesizing "body of def without specified type"))) ) in
        let notations =
          match head with
          | Head_name _ -> notations
          | Head_notation { pattern; _ } ->
              check_pattern_vars_unique pattern;
              (def, const) :: notations in
        (cdef :: cdefs, notations))
      defs ([], []) in
  let result = Core.Command.execute (Def cdefs) in
  List.iter
    (fun ((const, _), { name; loc; tm; _ }) ->
      let const = Lazy.force const in
      register_data_constructors ?loc name const;
      register_data_fields ?loc name const;
      register_syntax_constructors ?loc name const tm)
    (List.combine cdefs defs);
  List.iter
    (fun ({ head; loc; _ }, const) ->
      match head with
      | Head_name _ -> ()
      | Head_notation { fixity; pattern; _ } ->
          let name = notation_name pattern in
          register_notation ~loc ~name ~fixity ~pattern ~key:(`Constant (Lazy.force const))
            ~val_vars:(User.Pattern.value_vars pattern))
    notations;
  result

(* Most execution of commands we can do here, but there are a couple things where we need to call out to the executable: noting when an effectual action like 'echo' is taken (for recording warnings in compiled files), and loading another file.  So this function takes a couple of callbacks as arguments. *)
let exec_defs ?(existing = StringsMap.empty) (defs : def list) =
  exec_defs_with Global.run_command ~existing defs

let exec_defs_current ?(existing = StringsMap.empty) (defs : def list) =
  exec_defs_with Global.run_command_current ~existing defs

let with_private_export private_ f =
  if not private_ then f ()
  else
    let export = Scope.get_export () in
    match f () with
    | ans ->
        Scope.set_export export;
        ans
    | exception e ->
        Scope.set_export export;
        raise e

let flatten_parameters (params : Parameter.t list) =
  List.concat_map
    (fun ({ names; ty; _ } : Parameter.t) ->
      List.map
        (fun (name, _) -> { wslparen = []; names = [ (name, []) ]; wscolon = []; ty; wsrparen = [] })
        names)
    params

let prefix_def_params prefix ({ parameters; _ } as def : def) = { def with parameters = prefix @ parameters }
let prefix_defs_params prefix defs = List.map (prefix_def_params prefix) defs

let module_parameter_terms params =
  List.map
    (fun ({ names; _ } : Parameter.t) ->
      match names with
      | [ (Some x, _) ] -> ident_tm x
      | [ (None, _) ] ->
          fatal
            (Invalid_notation_pattern
               "module parameters participating in module application must be named")
      | _ -> fatal (Anomaly "flatten_parameters produced grouped module parameter"))
    params

let string_of_term_as_arg tm = "(" ^ string_of_term tm ^ ")"

let build_constant_app_term head args =
  parse_generated_term
    (String.concat " " (string_of_public_name head :: List.map string_of_term_as_arg args))

let hidden_module_segment = function
  | ".constructors" | ".fields" | ".module" -> true
  | _ -> false

let public_module_entry path = not (List.exists hidden_module_segment path)

let process_module_modifiers ({ filter; renaming } : module_modifiers) =
  let module Language = Yuujinchou.Language in
  let ops =
    (match filter with
    | None -> []
    | Some (`Using (_, { items; _ })) ->
        [
          (match List.map (fun (path, _) -> Language.only path) items with
          | [] -> Language.id
          | [ op ] -> op
          | ops -> Language.union ops);
        ]
    | Some (`Hiding (_, { items; _ })) ->
        List.map (fun (path, _) -> Language.except path) items)
    @
    match renaming with
    | None -> []
    | Some (_, _, items, _) -> List.map (fun { source; target; _ } -> Language.renaming source target) items
  in
  match ops with
  | [] -> Language.id
  | [ op ] -> op
  | ops -> Language.seq ops

let module_file_of_path path = String.concat "/" path ^ ".ny"

let module_alias_defs ~name ~params ~source ~source_trie ~applied_args =
  Seq.fold_left
    (fun defs (rel, ((data, loc), _)) ->
      match data with
      | `Constant _ when public_module_entry rel ->
          let full_name = name @ rel in
          {
            wsdef = [];
            head = Head_name full_name;
            name = full_name;
            loc;
            wshead = [];
            parameters = params;
            ty = None;
            wscoloneq = [];
            tm = build_constant_app_term (source @ rel) (applied_args @ module_parameter_terms params);
          }
          :: defs
      | _ -> defs)
    [] (Trie.to_seq source_trie)
  |> List.rev

let register_module_alias_syntax ~name ~source_trie =
  Seq.iter
    (fun (rel, ((data, loc), _)) ->
      match data with
      | `Constant c when public_module_entry rel ->
          let full_name = name @ rel in
          register_data_constructors ?loc full_name c;
          register_data_fields ?loc full_name c
      | _ -> ())
    (Trie.to_seq source_trie)

let execute ~(action_taken : unit -> unit) ~(get_file : string -> Scope.trie) (cmd : Command.t) :
    int option * (int * int * int) list =
  (match (Origin.current (), needs_interactive cmd) with
  | Top, true | File _, true -> fatal (Forbidden_interactive_command (to_string cmd))
  | _ -> ());
  match cmd with
  | Axiom { name; nonparam; loc; parameters; ty = Wrap ty; _ } ->
      Global.run_command ~holes_allowed:(Ok ()) @@ fun () ->
      (match name with
      | [ str ] ->
          if Option.is_some (deg_of_name str) then
            fatal (Invalid_constant_name (name, Some "that's a degeneracy name"))
      | _ -> ());
      Scope.check_name name loc;
      let const = Scope.define ?loc name in
      let (Processed_tel (params, ctx, _)) = process_tel Emp parameters in
      let parametric = Option.is_none nonparam in
      Core.Command.execute (Axiom { name = const; params; ty = process ctx ty; parametric })
  | TypeSig _ | Clause _ -> fatal (Anomaly "top-level signatures and clauses must be batched")
  | Def defs | Data_decl defs | Record_decl defs -> exec_defs defs
  | Echo { tm = Wrap tm; eval; number; _ } -> (
      let module Scope_and_ctx = struct
        type t = Scope_and_ctx : (string option, 'a) Bwv.t * ('a, 'b) Ctx.t -> t
      end in
      let open Scope_and_ctx in
      let Scope_and_ctx (vars, ctx), run =
        match number with
        | None ->
            (Scope_and_ctx (Bwv.Emp, Ctx.empty), Global.run_command_then_undo ~holes_allowed:(Ok ()))
        | Some number ->
            let num = Global.find_hole number in
            let (Found_hole { instant; termctx; vars; parametric; _ }) = num in
            show_hole num;
            ( Scope_and_ctx (vars, Norm.eval_ctx termctx),
              Global.rewind_command_then_undo ~parametric ~holes_allowed:(Ok ()) instant ) in
      run @@ fun () ->
      let rtm = process vars tm in
      action_taken ();
      match rtm.value with
      | Synth stm ->
          Readback.Displaying.run ~env:true @@ fun () ->
          let ctm, ety = Check.synth (Kinetic `Nolet) ctx { value = stm; loc = rtm.loc } in
          let btm =
            if eval then
              let etm = Norm.eval_term (Ctx.env ctx) ctm in
              readback_at ctx etm ety
            else ctm in
          let bty = readback_at ctx ety (Value.universe D.zero) in
          let utm = unparse (Names.of_ctx ctx) btm No.Interval.entire No.Interval.entire in
          let uty = unparse (Names.of_ctx ctx) bty No.Interval.entire No.Interval.entire in
          PPrint.(
            ToChannel.pretty 1.0 (Display.columns ()) stdout
              (hang 2
                 (pp_complete_term (Wrap utm) `None
                 ^^ hardline
                 ^^ Token.pp Colon
                 ^^ blank 1
                 ^^ pp_complete_term (Wrap uty) `None)));
          print_newline ();
          print_newline ();
          (None, fun _ -> None)
      | _ -> fatal (Nonsynthesizing ("argument of " ^ if eval then "echo" else "synth")))
  | Notation { fixity; loc; pattern; head; args; _ } ->
      Global.run_command ~holes_allowed:(Error (to_string cmd)) @@ fun () ->
      let key =
        match head with
        | `Constr c -> `Constr (Constr.intern c, List.length args)
        | `Constant c -> (
            match Scope.lookup_constr c with
            | Some (c, _) -> `Constr (c, List.length args)
            | None -> (
                match Scope.lookup c with
                | Some c -> `Constant c
                | None -> fatal (Invalid_notation_head (String.concat "." c)))) in
      check_notation_args args pattern;
      register_notation ~loc ~name:(notation_name pattern) ~fixity ~pattern ~key
        ~val_vars:(List.map fst args);
      (None, fun _ -> None)
  | Fixity_decl { fixity; loc; name; pattern; val_vars; _ } ->
      Global.run_command ~holes_allowed:(Error (to_string cmd)) @@ fun () ->
      let key =
        match Scope.lookup_constr name with
        | Some (c, _) -> `Constr (c, List.length val_vars)
        | None -> (
            match Scope.lookup name with
            | Some c -> `Constant c
            | None -> fatal (Invalid_notation_head (String.concat "." name)))
      in
      register_notation ~loc ~name:(notation_name pattern) ~fixity ~pattern ~key ~val_vars;
      (None, fun _ -> None)
  | Import { export; origin; op; _ } ->
      Global.run_command ~holes_allowed:(Error (to_string cmd)) @@ fun () ->
      let trie =
        match origin with
        | `File file ->
            if FilePath.check_extension file "ny" then emit (Library_has_extension file);
            let file = FilePath.add_extension file "ny" in
            get_file file
        | `Path path -> Trie.find_subtree path (Scope.get_visible ()) in
      let trie =
        match op with
        | Some (_, op) -> Scope.Mod.modify (process_modifier op) trie
        | None -> trie in
      if export then Scope.include_subtree ([], trie) else Scope.import_subtree ([], trie);
      (None, fun _ -> None)
  | Chdir { dir; _ } ->
      let newdir = Effect.perform (Chdir dir) in
      emit (Directory_changed newdir);
      (None, [])
  | Solve data ->
      let (Found_hole { instant; parametric; _ } as found) = Global.find_hole data.number in
      Global.rewind_command ~parametric ~holes_allowed:(Ok ()) instant @@ fun () ->
      let (Global.Found_hole
             { meta; instant = _; termctx; ty; status; vars; li; ri; parametric = _ }) =
        found in
      let (Wrap tm) = data.tm in
      let ptm = process vars tm in
      (* We set the hole location offset to the start of the *term*, so that ProofGeneral can create hole overlays in the right places when solving a hole and creating new holes. *)
      let tmloc = ptm.loc <|> Anomaly "missing location in solve" in
      let offset = (fst (split tmloc)).offset in
      (* Now we typecheck the supplied term. *)
      let ctx = Norm.eval_ctx termctx in
      let ety = Norm.eval_term (Ctx.env ctx) ty in
      let ctm = Check.check status ctx ptm ety in
      Global.set_meta meta ~tm:ctm;
      let buf = Buffer.create 20 in
      PPrint.ToBuffer.compact buf (pp_complete_term data.tm `None);
      ( Reporter.try_with ~fatal:(fun _ ->
            data.tm <- Wrap (parenthesize tm);
            data.parenthesized <- true)
      @@ fun () ->
        let _ =
          TermParse.Term.parse ~li ~ri (`String { content = Buffer.contents buf; title = None })
        in
        () );
      (Some offset, fun h -> Some (Code.Hole_solved h))
  | Split data ->
      let (Found_hole { instant; termctx; ty; vars; parametric; _ }) =
        Global.find_hole data.number in
      Global.rewind_command ~parametric ~holes_allowed:(Ok ()) instant @@ fun () ->
      (* We have to generate a bunch of holes, possibly in different tightness intervals. *)
      let hole li ri = locate_opt None (Hole { li; ri; num = ref (-1); ws = []; contents = None }) in
      let ehole = hole No.Interval.entire No.Interval.entire in
      let ctx = Norm.eval_ctx termctx in
      let _, names = Names.uniquify_vars vars in
      let term =
        match data.tms with
        | [ (_, Wrap { value = Placeholder _; _ }) ] -> (
            let ety = Norm.eval_term (Ctx.env ctx) ty in
            match View.view_type ety "split" with
            | Canonical (_, Pi (_, _, doms, _), _, _) ->
                let dim = CubeOf.dim doms in
                let cube =
                  match D.compare_zero dim with
                  | Zero -> `Normal
                  | Pos _ -> `Cube in
                (* Uniquify the variable names relative to the context *)
                let module NameState = Monad.State (struct
                  type t = Names.wrapped
                end) in
                let module M = Mbwd.Monadic (NameState) in
                let xs, _ =
                  M.mmapM
                    (fun [ x ] ->
                      let open Monad.Ops (NameState) in
                      let* (Wrap names) = NameState.get in
                      let x, names = Names.add_cube dim names x in
                      let* () = NameState.put (Wrap names) in
                      return x)
                    [ Domvars.get_pi_vars ctx cube Emp ety ]
                    (Wrap names) in
                let vars =
                  unparse_abs
                    (Bwd.map (fun x -> (x, `Explicit)) xs)
                    { strictness = No.Nonstrict; endpoint = No.minus_omega }
                    (No.minusomega_le No.plus_omega) No.minusomega_lt_plusomega in
                locate_opt None
                @@
                (match cube with
                | `Normal ->
                    prefix ~notn:Builtins.abs
                      ~inner:
                        (Multiple
                           ( Left (Token.Lambda, ([], None)),
                             Emp <: Term vars,
                             Left (Token.Arrow, ([], None)) ))
                      ~last:ehole ~right_ok:(No.le_refl No.minus_omega)
                | `Cube ->
                    infix ~notn:Builtins.cubeabs ~first:vars
                      ~inner:(Single (Left (Token.DblMapsto, ([], None))))
                      ~last:ehole ~left_ok:(No.le_refl No.minus_omega)
                      ~right_ok:(No.le_refl No.minus_omega))
            | Canonical (_, Codata { eta; fields; _ }, ins, _) -> (
                let m = cod_left_ins ins in
                let do_field : type a n et.
                    (a * n * et) Term.CodatafieldAbwd.entry ->
                    (string * string list) list ->
                    (string * string list) list =
                 fun (Term.CodatafieldAbwd.Entry (fld, cdf)) acc ->
                  match cdf with
                  | Lower _ -> (Field.to_string fld, []) :: acc
                  | Higher _ ->
                      let i = Field.dim fld in
                      let pbijs = List.of_seq (all_pbij_between m i) in
                      List.fold_right
                        (fun (Pbij_between pbij) acc ->
                          (Field.to_string fld, strings_of_pbij pbij) :: acc)
                        pbijs acc in
                let fields = Bwd.fold_right do_field fields [] in
                match eta with
                | Eta ->
                    let inner =
                      Multiple
                        ( Left (LParen, ([], None)),
                          Bwd_extra.intersperse (tok (Op ","))
                            (Bwd_extra.of_list_map
                               (fun (fld, pbij) ->
                                 if List.length pbij > 0 then
                                   fatal (Anomaly "record type has higher field");
                                 Term
                                   (locate_opt None
                                      (infix ~notn:Builtins.coloneq
                                         ~first:(locate_opt None (Ident ([ fld ], [])))
                                         ~inner:(Single (Left (Coloneq, ([], None))))
                                         ~last:ehole ~left_ok:(No.le_refl No.minus_omega)
                                         ~right_ok:(No.le_refl No.minus_omega))))
                               fields),
                          Left (RParen, ([], None)) ) in
                    locate_opt None @@ outfix ~notn:parens ~inner
                | Noeta ->
                    let inner_fields =
                      List.fold_left
                        (fun acc (fld, pbij) ->
                          let acc = if acc = Emp then acc else acc <: tok (Op ";") in
                          acc
                          <: Term
                               (locate_opt None
                                  (if List.is_empty pbij && not (Lexer.all_digits fld) then
                                     Ident ([ fld ], [])
                                   else HigherField (fld, pbij, [])))
                          <: tok (Op "=")
                          <: Term ehole)
                        (Emp <: tok LBrace) fields in
                    let inner =
                      Multiple
                        (Left (Record, ([], None)), inner_fields, Left (RBrace, ([], None))) in
                    locate_opt None @@ outfix ~notn:Builtins.comatch ~inner)
            | Canonical (_, Data { constrs = Snoc (Emp, (constr, Dataconstr { args; _ })); _ }, _, _)
              ->
                let nargs = Fwn.to_int (Term.Telescope.length args) in
                unparse_spine names (`Constr constr)
                  (Bwd.init nargs (fun _ -> { unparse = (fun li ri -> hole li ri) }))
                  No.Interval.entire No.Interval.entire
            | Canonical (_, Data { constrs = Snoc (Emp, (_, Higher_dataconstr _)); _ }, _, _) ->
                fatal (Invalid_split (`Goal, "higher inductive types"))
            | Canonical (_, Data { constrs = Emp; _ }, _, _) ->
                fatal (Invalid_split (`Goal, "empty datatype"))
            | Canonical (_, Data { constrs = Snoc (Snoc (_, _), _); _ }, _, _) ->
                fatal (Invalid_split (`Goal, "datatype with multiple constructors"))
            | Canonical (_, UU _, _, _) -> fatal (Invalid_split (`Goal, "universe"))
            | Neutral _ -> fatal (Invalid_split (`Goal, "neutral")))
        | _ ->
            let tok t : observation = Token (t, ([], None)) in
            let comma_tms =
              List.tl
                (let open Monad.Ops (Monad.List) in
                 let* wscomma, Wrap tm = data.tms in
                 [ Token (Op ",", (wscomma, None)); Term tm ]) in
            (* We have a list of terms and we need to produce a multiple match.  We use a list monad to produce all possible combinations of constructors for all the types of all the terms, with a boolean state outside the list to track, whether it contains any higher-dimensional matches and thus should use a ⤇ instead of a ↦.  And we use a Names state *inside* the list to uniquify variables separately in each branch. *)
            let module HigherBranch = Monad.State (Bool) in
            let module Branches = Monad.ListT (HigherBranch) in
            let module NameBranches =
              Monad.StateT
                (Branches)
                (struct
                  type t = Names.wrapped
                end)
            in
            let open Monad.Ops (NameBranches) in
            let rec constr_args : type a p ap n k.
                n Names.t ->
                k D.t ->
                ?acc:unparser Bwd.t ->
                (a, p, ap) Term.Telescope.t ->
                unparser Bwd.t * Names.wrapped =
             fun names dim ?(acc = Emp) -> function
               | Emp -> (acc, Wrap names)
               | Ext (x, _, args) ->
                   let x, names = Names.add_cube dim names x in
                   constr_args names dim
                     ~acc:(Snoc (acc, { unparse = (fun _ _ -> unparse_var x) }))
                     args in
            let rec go = function
              | [] ->
                  let* higher = NameBranches.stateless (Branches.lift HigherBranch.get) in
                  let mapsto = if higher then Token.DblMapsto else Mapsto in
                  return [ tok mapsto; Term ehole ]
              | (_, Wrap tm) :: tms -> (
                  match process vars tm with
                  | { value = Synth rtm; loc } -> (
                      let _, sty = Check.synth (Kinetic `Nolet) ctx (locate_opt loc rtm) in
                      match View.view_type sty "split" with
                      | Canonical (_, Data { dim; constrs; _ }, _, _) ->
                          let* () =
                            match D.compare_zero dim with
                            | Zero -> return ()
                            | Pos _ ->
                                NameBranches.stateless (Branches.lift (HigherBranch.put true)) in
                          let* c, dc =
                            NameBranches.stateless (HigherBranch.return (Bwd.to_list constrs)) in
                          let* (Wrap names) = NameBranches.get in
                          let cargs, newnames =
                            match dc with
                            | Dataconstr { args; _ } -> constr_args names dim args
                            | Higher_dataconstr _ ->
                                fatal (Invalid_split (`Term, "higher inductive types"))
                          in
                          let* () = NameBranches.put newnames in
                          let first =
                            Term
                              (unparse_spine names (`Constr c) cargs No.Interval.entire
                                 No.Interval.entire) in
                          let* rest = go tms in
                          if List.length rest = 2 then return (first :: rest)
                          else return (first :: tok (Op ",") :: rest)
                      | _ -> fatal (Invalid_split (`Term, "non-datatype")))
                  | _ -> fatal (Nonsynthesizing "splitting term")) in
            let lines, _ = go data.tms (Wrap names) false in
            locate_opt None
            @@ outfix ~notn:Builtins.implicit_mtch
                 ~inner:
                   (Multiple
                      ( Left (Match, ([], None)),
                        Emp
                        <@ comma_tms
                        <: tok LBracket
                        <@ List.flatten (List.map (fun (line, _) -> tok (Op "|") :: line) lines),
                        Left (RBracket, ([], None)) )) in
      let buf = Buffer.create 10 in
      let s = Display.get () in
      Display.run ~init:{ s with holes = `Without_number } @@ fun () ->
      PPrint.(ToBuffer.pretty 1.0 (Display.columns ()) buf (pp_complete_term (Wrap term) `None));
      let content = Buffer.contents buf in
      let ptm = TermParse.Term.(final (parse (`String { title = None; content }))) in
      let disp = Display.get () in
      Display.run ~init:{ disp with holes = `Without_number } @@ fun () ->
      data.printed_term <- pp_complete_term ptm `None;
      (None, fun _ -> Some (Code.Split_term data.printed_term))
  | Show { what; _ } ->
      action_taken ();
      (match what with
      | `Hole (_, number) -> show_hole (Global.find_hole number)
      | `Holes -> (
          match Global.all_holes () with
          | Emp -> emit No_open_holes
          | holes -> Mbwd.miter (fun [ h ] -> show_hole h) [ holes ]));
      (None, [])
  | Display { what; _ } ->
      (match what with
      | `Chars (_, chars, _) ->
          let chars = Display.modify_chars chars in
          emit (Display_set ("chars", Display.to_string (chars :> Display.values)))
      | `Function_boundaries (_, _, fb, _) ->
          let fb = Display.modify_function_boundaries fb in
          emit (Display_set ("function boundaries", Display.to_string (fb :> Display.values)))
      | `Type_boundaries (_, _, tb, _) ->
          let tb = Display.modify_type_boundaries tb in
          emit (Display_set ("type boundaries", Display.to_string (tb :> Display.values))));
      (None, [])
  | Pragma _ -> (None, [])
  | Undo { count; _ } ->
      for _ = 1 to count do
        match Origin.undo () with
        | `Ok -> ()
        | `No_past -> fatal Not_enough_to_undo
        | `Not_interactive -> fatal (Forbidden_interactive_command "undo")
      done;
      emit (Commands_undone count);
      (None, [])
  | Section { prefix; _ } ->
      Global.run_command ~holes_allowed:(Error (to_string cmd)) @@ fun () ->
      Scope.start_section prefix;
      (None, fun _ -> Some (Section_opened prefix))
  | Fmt _ -> (None, [])
  | End _ -> (
      Global.run_command ~holes_allowed:(Error (to_string cmd)) @@ fun () ->
      match Scope.end_section () with
      | Some prefix -> (None, fun _ -> Some (Section_closed prefix))
      | None -> fatal No_such_section)
  | Quit _ -> fatal (Quit None)
  | Bof _ -> (None, [])
  | Eof -> fatal (Anomaly "EOF cannot be executed")

let tightness_of_fixity : type left tight right. (left, tight, right) fixity -> string option =
  function
  | Infix tight
  | Infixl tight
  | Infixr tight
  | Prefix tight
  | Prefixr tight
  | Postfix tight
  | Postfixl tight -> Some (No.to_string tight)
  | Outfix -> None

let rec pp_parameters : Whitespace.t list -> Parameter.t list -> PPrint.document * Whitespace.t list
    =
 fun prews params ->
  let open PPrint in
  match params with
  | [] -> (empty, prews)
  | { wslparen; names; wscolon; ty; wsrparen } :: params ->
      let pnames, wnames =
        List.fold_left
          (fun (accum, prews) (name, wsname) ->
            (accum ^^ group (optional (pp_ws `Break) prews ^^ pp_var name), Some wsname))
          (empty, None) names in
      let pparams, wparams = pp_parameters wsrparen params in
      ( group
          (pp_ws `Break prews
          ^^ group
               (Token.pp LParen
               ^^ pp_ws `None wslparen
               ^^ group pnames
               ^^ optional (pp_ws `Break) wnames)
          ^^ Token.pp Colon
          ^^ pp_ws `Nobreak wscolon
          ^^ pp_complete_term ty `None
          ^^ Token.pp RParen)
        ^^ pparams,
        wparams )

let pp_def_head : def_head -> space * PPrint.document * Whitespace.t list =
fun head ->
  let open PPrint in
  match head with
  | Head_name name -> (`Nobreak, utf8string (String.concat "." name), [])
  | Head_notation { fixity; wslparen; wstight; wsellipsis; wsrparen; wspatlparen; pattern } ->
      let ppat, wpat = User.pp_pattern pattern in
      let ptight, ws =
        match tightness_of_fixity fixity with
        | Some str ->
            ( Token.pp LParen
              ^^ pp_ws `None wslparen
              ^^ string str
              ^^ pp_ws `None wstight
              ^^ Token.pp RParen,
              wsrparen )
        | None -> (empty, []) in
      ( (match tightness_of_fixity fixity with Some _ -> `None | None -> `Nobreak),
        ptight
        ^^ pp_ws `Break ws
        ^^ Token.pp LParen
        ^^ pp_ws `None wspatlparen
        ^^ (match fixity with
           | Infixl _ | Postfixl _ -> Token.pp Ellipsis ^^ pp_ws `Nobreak wsellipsis
           | _ -> empty)
        ^^ group (hang 2 ppat)
        ^^ (match fixity with
           | Infixr _ | Prefixr _ ->
               pp_ws `Nobreak wpat ^^ Token.pp Ellipsis ^^ pp_ws `None wsellipsis
           | _ -> pp_ws `None wpat)
        ^^ Token.pp RParen,
        [] )

let pp_term_list items =
  let open PPrint in
  let rec go accum = function
    | [] -> (accum, [])
    | [ Wrap tm ] ->
        let ptm, wtm = pp_term tm in
        (accum ^^ ptm, wtm)
    | Wrap tm :: items ->
        let ptm, wtm = pp_term tm in
        go (accum ^^ ptm ^^ pp_ws `Break wtm ^^ Token.pp (Op ";") ^^ blank 1) items
  in
  go empty items

let pp_record_fields fields =
  let open PPrint in
  let rec go accum = function
    | [] -> (accum, [])
    | [ (fld, Wrap ty) ] ->
        let pty, wty = pp_term ty in
        (accum ^^ utf8string fld ^^ blank 1 ^^ Token.pp Colon ^^ blank 1 ^^ pty, wty)
    | (fld, Wrap ty) :: fields ->
        let pty, wty = pp_term ty in
        go
          ( accum
          ^^ utf8string fld
          ^^ blank 1
          ^^ Token.pp Colon
          ^^ blank 1
          ^^ pty
          ^^ pp_ws `Break wty
          ^^ Token.pp (Op ";")
          ^^ blank 1 )
          fields
  in
  go empty fields

let rec pp_data_decl_defs :
    Token.t ->
    Whitespace.t list option ->
    def list ->
    PPrint.document ->
    PPrint.document * Whitespace.t list =
 fun tok prews defs accum ->
  let open PPrint in
  match defs with
  | [] -> (accum, Option.value ~default:[] prews)
  | { wsdef; name; wshead; parameters; ty; tm; _ } :: defs -> (
      match (ty, extract_data_tm tm) with
      | Some (wscolon, Wrap ty), Some constrs ->
          let prews =
            match tok with
            | And -> Option.fold ~some:(Whitespace.normalize 2) ~none:[ `Newlines 2 ] prews
            | _ -> Option.value ~default:[] prews
          in
          let accum_prews = accum ^^ pp_ws `None prews in
          let pparams, wparams = pp_parameters wshead parameters in
          let ty, rest = split_ending_whitespace ty in
          let pconstrs, wconstrs = pp_term_list constrs in
          let body =
            Token.pp Where
            ^^ blank 1
            ^^ Token.pp LBrace
            ^^ (if List.is_empty constrs then empty else blank 1 ^^ pconstrs ^^ pp_ws `None wconstrs ^^ blank 1)
            ^^ Token.pp RBrace
          in
          pp_data_decl_defs And (Some []) defs
            ( accum_prews
            ^^ group
                 (Token.pp tok
                 ^^ pp_ws `Nobreak wsdef
                 ^^ utf8string (String.concat "." name)
                 ^^ group pparams
                 ^^ pp_ws `Break wparams
                 ^^ Token.pp Colon
                 ^^ pp_ws `Nobreak wscolon
                 ^^ pp_complete_term (Wrap ty) `None
                 ^^ pp_ws `Break rest
                 ^^ body) )
      | _ -> fatal (Anomaly "ill-formed data declaration for printing"))

let rec pp_record_decl_defs :
    Token.t ->
    Whitespace.t list option ->
    def list ->
    PPrint.document ->
    PPrint.document * Whitespace.t list =
 fun tok prews defs accum ->
  let open PPrint in
  match defs with
  | [] -> (accum, Option.value ~default:[] prews)
  | { wsdef; name; wshead; parameters; ty; tm; _ } :: defs -> (
      match (ty, extract_simple_record_tm tm) with
      | Some (wscolon, Wrap ty), Some fields ->
          let prews =
            match tok with
            | And -> Option.fold ~some:(Whitespace.normalize 2) ~none:[ `Newlines 2 ] prews
            | _ -> Option.value ~default:[] prews
          in
          let accum_prews = accum ^^ pp_ws `None prews in
          let pparams, wparams = pp_parameters wshead parameters in
          let ty, rest = split_ending_whitespace ty in
          let pfields, wfields = pp_record_fields fields in
          let body =
            Token.pp Where
            ^^ blank 1
            ^^ Token.pp LBrace
            ^^ (if List.is_empty fields then empty
               else blank 1
                    ^^ Token.pp Field_kw
                    ^^ blank 1
                    ^^ pfields
                    ^^ pp_ws `None wfields
                    ^^ blank 1)
            ^^ Token.pp RBrace
          in
          pp_record_decl_defs And (Some []) defs
            ( accum_prews
            ^^ group
                 (Token.pp tok
                 ^^ pp_ws `Nobreak wsdef
                 ^^ utf8string (String.concat "." name)
                 ^^ group pparams
                 ^^ pp_ws `Break wparams
                 ^^ Token.pp Colon
                 ^^ pp_ws `Nobreak wscolon
                 ^^ pp_complete_term (Wrap ty) `None
                 ^^ pp_ws `Break rest
                 ^^ body) )
      | _ -> fatal (Anomaly "ill-formed record declaration for printing"))

let rec pp_defs :
    Token.t ->
    Whitespace.t list option ->
    def list ->
    PPrint.document ->
    PPrint.document * Whitespace.t list =
 fun tok prews defs accum ->
  let open PPrint in
  match defs with
  | [] -> (accum, Option.fold ~some:(fun x -> x) ~none:[] prews)
  | { wsdef; head; name = _; loc = _; wshead; parameters; ty; wscoloneq; tm = Wrap tm } :: defs ->
      let prews =
        match tok with
        | And -> Option.fold ~some:(Whitespace.normalize 2) ~none:[ `Newlines 2 ] prews
        | _ -> Option.value ~default:[] prews in
      let accum_prews = accum ^^ pp_ws `None prews in
      let head_space, phead, whead = pp_def_head head in
      let pparams, wparams = pp_parameters (whead @ wshead) parameters in
      (* The type is always displayed in term mode, with a wrapping break allowed before the colon. *)
      let gty, wty =
        match ty with
        | Some (wscolon, Wrap ty) ->
            let pty, wty = pp_term ty in
            (pp_ws `Break wparams ^^ Token.pp Colon ^^ pp_ws `Nobreak wscolon ^^ group pty, wty)
        | None -> (empty, wparams) in
      let params_and_ty =
        group
          (hang 2
             (Token.pp tok
             ^^ pp_ws head_space wsdef
             ^^ phead
             ^^ group pparams
             ^^ gty)) in
      let coloneq = Token.pp Coloneq ^^ pp_ws `Nobreak wscoloneq in
      if is_case tm then
        (* If the term is a case tree, we display it in case mode.  In this case, the principal breaking points are those in the term's case tree, and we group its "intro" with the def and type. *)
        let itm, ptm, wtm = pp_case `Nontrivial tm in
        pp_defs And (Some wtm) defs
          (accum_prews
          ^^ group
               (group
                  (params_and_ty
                  ^^ nest 2 (pp_ws `Break wty ^^ group (coloneq ^^ group (hang 2 itm))))
               ^^ ptm))
      else
        (* If the term is not a case tree, then we display it in term mode, and the principal breaking points are before the colon (if any), before the coloneq, and before the "in" (though that will be rare, since "in" is so short). *)
        let ptm, wtm = pp_term tm in
        pp_defs And (Some wtm) defs
          (accum_prews
          ^^ group (params_and_ty ^^ nest 2 (pp_ws `Break wty ^^ coloneq ^^ group (hang 2 ptm))))

let pp_attribute : type a.
    (a -> Whitespace.t list list -> PPrint.document) -> a attribute -> PPrint.document =
 fun pp { wshash; wslparen; loc = _; attr; wsattr; wsrparen } ->
  let open PPrint in
  Token.pp (Op "#")
  ^^ pp_ws `None wshash
  ^^ Token.pp LParen
  ^^ pp_ws `None wslparen
  ^^ pp attr wsattr
  ^^ Token.pp RParen
  ^^ pp_ws `Nobreak wsrparen

let rec pp_where_block_doc ({ wswhere; wslbrace; first; rest; wsrbrace } : where_block) =
  let open PPrint in
  let rec pp_local_cmd = function
    | Local_type_sig sig_cmd -> pp_type_sig_doc sig_cmd
    | Local_clause clause -> pp_clause_doc clause
  and pp_local_cmds accum prews = function
    | [] -> (accum, Option.value ~default:[] prews)
    | (wssemi, cmd) :: rest ->
        let pcmd, wcmd = pp_local_cmd cmd in
        pp_local_cmds
          ( accum
          ^^ optional (pp_ws `Break) prews
          ^^ Token.pp (Op ";")
          ^^ pp_ws `Break wssemi
          ^^ pcmd )
          (Some wcmd) rest
  and pp_type_sig_doc ({ name; loc = _; wsname; wscolon; ty = Wrap ty } : type_sig) =
    let ty, rest = split_ending_whitespace ty in
    ( group
        (utf8string (string_of_public_name name)
        ^^ pp_ws `Nobreak wsname
        ^^ Token.pp Colon
        ^^ pp_ws `Nobreak wscolon
        ^^ pp_complete_term (Wrap ty) `None),
      rest )
  and pp_clause_doc ({ lhs = Wrap lhs; wseq; tm = Wrap tm; where_block } : clause) =
    let lhs, _wslhs = split_ending_whitespace lhs in
    let tm, rest = split_ending_whitespace tm in
    let pwhere, wwhere =
      match where_block with
      | None -> (empty, rest)
      | Some where_block ->
          let pwhere, wwhere = pp_where_block_doc where_block in
          (pp_ws `Break rest ^^ pwhere, wwhere)
    in
    if is_case tm then
      let itm, ptm, wtm = pp_case `Nontrivial tm in
      ( group
          (pp_complete_term (Wrap lhs) `None
          ^^ pp_ws `Break []
          ^^ Token.pp (Op "=")
          ^^ nest 2 (pp_ws `Break wseq ^^ group (hang 2 itm))
          ^^ ptm
          ^^ pwhere),
        wwhere @ wtm )
    else
      ( group
          (pp_complete_term (Wrap lhs) `None
          ^^ pp_ws `Break []
          ^^ Token.pp (Op "=")
          ^^ nest 2 (pp_ws `Break wseq ^^ group (hang 2 (pp_complete_term (Wrap tm) `None)))
          ^^ pwhere),
        wwhere )
  in
  let pfirst, wfirst = pp_local_cmd first in
  let prest, wlast = pp_local_cmds empty (Some wfirst) rest in
  ( group
      (Token.pp Where
      ^^ pp_ws `Nobreak wswhere
      ^^ Token.pp LBrace
      ^^ pp_ws `Break wslbrace
      ^^ pfirst
      ^^ prest
      ^^ pp_ws `Break wlast
      ^^ Token.pp RBrace),
    wsrbrace )

and pp_type_sig_doc ({ name; loc = _; wsname; wscolon; ty = Wrap ty } : type_sig) =
  let open PPrint in
  let ty, rest = split_ending_whitespace ty in
  ( group
      (utf8string (string_of_public_name name)
      ^^ pp_ws `Nobreak wsname
      ^^ Token.pp Colon
      ^^ pp_ws `Nobreak wscolon
      ^^ pp_complete_term (Wrap ty) `None),
    rest )

and pp_clause_doc ({ lhs = Wrap lhs; wseq; tm = Wrap tm; where_block } : clause) =
  let open PPrint in
  let lhs, _wslhs = split_ending_whitespace lhs in
  let tm, rest = split_ending_whitespace tm in
  let pwhere, wwhere =
    match where_block with
    | None -> (empty, rest)
    | Some where_block ->
        let pwhere, wwhere = pp_where_block_doc where_block in
        (pp_ws `Break rest ^^ pwhere, wwhere)
  in
  if is_case tm then
    let itm, ptm, wtm = pp_case `Nontrivial tm in
    ( group
        (pp_complete_term (Wrap lhs) `None
        ^^ pp_ws `Break []
        ^^ Token.pp (Op "=")
        ^^ nest 2 (pp_ws `Break wseq ^^ group (hang 2 itm))
        ^^ ptm
        ^^ pwhere),
      wwhere @ wtm )
  else
    ( group
        (pp_complete_term (Wrap lhs) `None
        ^^ pp_ws `Break []
        ^^ Token.pp (Op "=")
        ^^ nest 2 (pp_ws `Break wseq ^^ group (hang 2 (pp_complete_term (Wrap tm) `None)))
        ^^ pwhere),
      wwhere )

(* We only print commands that can appear in source files or for which ProofGeneral may need reformatting info (e.g. solve). *)
let pp_command : t -> PPrint.document * Whitespace.t list =
fun cmd ->
  let open PPrint in
  let rec go cmd =
    let indent = Scope.count_sections () * 2 in
    match cmd with
    | Axiom { wsaxiom; nonparam; name; loc = _; wsname; parameters; wscolon; ty = Wrap ty } ->
        let pparams, wparams = pp_parameters wsname parameters in
        let ty, rest = split_ending_whitespace ty in
        ( indent,
          group
            (hang 2
               (Token.pp Axiom
               ^^ pp_ws `Nobreak wsaxiom
               ^^ PPrint.optional
                    (pp_attribute (fun () ws ->
                         string "nonparametric" ^^ concat_map (pp_ws `None) ws))
                    nonparam
               ^^ utf8string (String.concat "." name)
               ^^ pparams
               ^^ pp_ws `Break wparams
               ^^ Token.pp Colon
               ^^ pp_ws `Nobreak wscolon
               ^^ pp_complete_term (Wrap ty) `None)),
          rest )
    | TypeSig sig_cmd ->
        let doc, rest = pp_type_sig_doc sig_cmd in
        (indent, doc, rest)
    | Clause clause ->
        let doc, rest = pp_clause_doc clause in
        (indent, doc, rest)
    | Def defs ->
        if defs_are_data_decl defs then
          let doc, ws = pp_data_decl_defs Data None defs empty in
          (indent, doc, ws)
        else if defs_are_record_decl defs then
          let doc, ws = pp_record_decl_defs Record None defs empty in
          (indent, doc, ws)
        else
          let doc, ws = pp_defs Def None defs empty in
          (indent, doc, ws)
    | Data_decl defs ->
        let doc, ws = pp_data_decl_defs Data None defs empty in
        (indent, doc, ws)
    | Record_decl defs ->
        let doc, ws = pp_record_decl_defs Record None defs empty in
        (indent, doc, ws)
    | Echo { wsecho; number; wsin; wsnumber; tm = Wrap tm; eval } ->
        let tm, rest = split_ending_whitespace tm in
        ( indent,
          hang 2
            (Token.pp (if eval then Echo else Synth)
            ^^ pp_ws `Nobreak wsecho
            ^^ optional
                 (fun n ->
                   Token.pp In
                   ^^ pp_ws `Nobreak wsin
                   ^^ string (string_of_int n)
                   ^^ pp_ws `Nobreak wsnumber)
                 number
            ^^ pp_complete_term (Wrap tm) `None),
          rest )
    | Notation
        {
          fixity;
          wsnotation;
          wslparen;
          wstight;
          wsellipsis;
          loc = _;
          wsrparen;
          pattern;
          wscoloneq;
          head;
          wshead;
          args;
        } ->
        let pargs, rest =
          match split_last args with
          | None ->
              let wshead, rest = Whitespace.split wshead in
              (pp_ws `None wshead, rest)
          | Some (args, (last, wslast)) ->
              let wslast, rest = Whitespace.split wslast in
              (* We "flow" the arguments of the head. *)
              let pargs, wargs =
                List.fold_left
                  (fun (acc, prews) (arg, wsarg) ->
                    (acc ^^ group (pp_ws `Break prews ^^ utf8string arg), wsarg))
                  (empty, wshead) args in
              (pargs ^^ group (pp_ws `Break wargs ^^ utf8string last) ^^ pp_ws `None wslast, rest)
        in
        let ppat, wpat = User.pp_pattern pattern in
        let notn_tight, ws =
          match tightness_of_fixity fixity with
          | Some str ->
              ( pp_ws `None wsnotation
                ^^ Token.pp LParen
                ^^ pp_ws `None wslparen
                ^^ string str
                ^^ pp_ws `None wstight
                ^^ Token.pp RParen,
                wsrparen )
          | None -> (empty, wsnotation) in
        ( indent,
          hang 2
            (Token.pp Notation
            ^^ notn_tight
            ^^ group
                 (group
                    (pp_ws `Break ws
                    ^^ (match fixity with
                       | Infixl _ | Postfixl _ -> Token.pp Ellipsis ^^ pp_ws `Nobreak wsellipsis
                       | _ -> empty)
                    ^^ group (hang 2 ppat))
                 ^^ (match fixity with
                    | Infixr _ | Prefixr _ ->
                        pp_ws `Nobreak wpat ^^ Token.pp Ellipsis ^^ pp_ws `Break wsellipsis
                    | _ -> pp_ws `Break wpat)
                 ^^ Token.pp Coloneq
                 ^^ pp_ws `Nobreak wscoloneq
                 ^^ group
                      (hang 2
                         ((match head with
                          | `Constr c -> pp_constr c
                          | `Constant c -> utf8string (String.concat "." c))
                         ^^ pargs)))),
          rest )
    | Fixity_decl { keyword; wsfixity; fixity; loc = _; name; wstight; wsname; pattern = _; val_vars = _ }
      ->
        let wsname, rest = Whitespace.split wsname in
        let tight =
          match tightness_of_fixity fixity with
          | Some tight -> tight
          | None -> fatal (Anomaly "fixity declaration without tightness")
        in
        ( indent,
          group
            (Token.pp (token_of_fixity_keyword keyword)
            ^^ pp_ws `Nobreak wsfixity
            ^^ string tight
            ^^ pp_ws `Nobreak wstight
            ^^ utf8string (string_of_public_name name)
            ^^ pp_ws `None wsname),
          rest )
    | Import { wsimport; export; origin; wsorigin; op } ->
        let op, rest =
          match op with
          | None ->
              let ws, rest = Whitespace.split wsorigin in
              (pp_ws `None ws, rest)
          | Some (wsbar, op) ->
              let pmod, wmod = pp_modifier op in
              let ws, rest = Whitespace.split wmod in
              ( pp_ws `Break wsorigin
                ^^ Token.pp (Op "|")
                ^^ pp_ws `Nobreak wsbar
                ^^ pmod
                ^^ pp_ws `None ws,
                rest ) in
        ( indent,
          group
            (nest 2
               (Token.pp (if export then Export else Import)
               ^^ pp_ws `Nobreak wsimport
               ^^ (match origin with
                  | `File file -> dquotes (utf8string file)
                  | `Path [] -> Token.pp Dot
                  | `Path path -> utf8string (String.concat "." path))
               ^^ op)),
          rest )
    | Chdir { wschdir; dir; wsdir } ->
        let ws, rest = Whitespace.split wsdir in
        ( indent,
          Token.pp Chdir ^^ pp_ws `Nobreak wschdir ^^ dquotes (utf8string dir) ^^ pp_ws `None ws,
          rest )
    | Pragma { wsopen; wsoptions; body; wsclose } ->
        let body =
          match List.rev body with
          | [] ->
              let ws, _ = Whitespace.split wsoptions in
              pp_ws `None ws
          | (last, wslast) :: revrest ->
              let wslast, _ = Whitespace.split wslast in
              let prefix =
                List.fold_left
                  (fun acc (tok, ws) -> acc ^^ Token.pp tok ^^ pp_ws `Nobreak ws)
                  empty (List.rev revrest)
              in
              prefix ^^ Token.pp last ^^ pp_ws `None wslast
        in
        let wsclose, rest = Whitespace.split wsclose in
        ( indent,
          Token.pp PragmaOpen
          ^^ pp_ws `Nobreak wsopen
          ^^ utf8string "OPTIONS"
          ^^ body
          ^^ Token.pp PragmaClose
          ^^ pp_ws `None wsclose,
          rest )
    | Solve { column; tm; _ } ->
        let (Wrap tm) = tm in
        (* We (mis)use pretty-printing of a solve *command* to actually just reformat the solving *term*.  This is appropriate since "solve" should never appear in a source file, and when it's called from ProofGeneral, PG knows that the reformatted return is the new string to insert at the hole location. *)
        let tm, rest = split_ending_whitespace tm in
        (* When called from ProofGeneral, the 'column' is the column number of the hole, so the reformatted term should "start at that indentation".  The best way I've thought of so far to mimic that effect is to reduce the margin by that amount, and then add extra indentation to each new line on the ProofGeneral end.  Also, section indents should be ignored when printing solve terms. *)
        (0, nest column (pp_complete_term (Wrap tm) `None), rest)
    | Split data ->
        (* Same with split, except here we've already done the printing. *)
        (0, data.printed_term, [])
    | Section { wssection; prefix; wsprefix; wscoloneq } ->
        let ws, rest = Whitespace.split wscoloneq in
        (* Since we pp a command *after* executing it, the indent is too large for the 'section' command. *)
        ( indent - 2,
          Token.pp Section
          ^^ pp_ws `Nobreak wssection
          ^^ utf8string (String.concat "." prefix)
          ^^ pp_ws `Nobreak wsprefix
          ^^ Token.pp Coloneq
          ^^ pp_ws `None ws,
          rest )
    | Fmt { instant; cmd; _ } ->
        (* We ignore the whitespace in the fmt command itself, since its purpose is to pretty-print the argument command.  We also ignore the current indent, since the recursive call takes place in the past and therefore will use the correct indentation for the past. *)
        Origin.rewind_command instant @@ fun () -> go cmd
    | End { wsend } ->
        let ws, rest = Whitespace.split wsend in
        (indent, Token.pp End ^^ pp_ws `None ws, rest)
    | Quit ws -> (indent, empty, ws)
    | Bof ws -> (indent, empty, ws)
    | Eof -> (indent, empty, [])
    (* These commands can't appear in a source file, and ProofGeneral doesn't need any reformatting info from them, so we display nothing.  In fact, in the case of Undo, PG uses this emptiness to determine that it should not replace any command in the buffer. *)
    | Show _ | Display _ | Undo _ -> (indent, empty, []) in
  (* Indent when inside of sections. *)
  let indent, doc, ws = go cmd in
  (* "nest" only has effect *after* linebreaks, so we have to separately indent the first line. *)
  (nest indent (blank indent ^^ doc), ws)

let parenthesized : t -> bool = function
  | Solve data -> data.parenthesized
  | _ -> false
