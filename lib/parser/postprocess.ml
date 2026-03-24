open Bwd
open Util
open Dim
open Core
open Raw
open Reporter
open Asai.Range
open Notation
open Monad.Ops (Monad.Maybe)
module StringMap = Map.Make (String)

(* Process a term into a list of strings, to be a multi-word attribute *)
let strings_of_term : type ls lt rs rt.
    (ls, lt, rs, rt) parse -> string list * Whitespace.t list list =
 fun tm ->
  let rec go : type ls lt rs rt.
      string list ->
      Whitespace.t list list ->
      (ls, lt, rs, rt) parse ->
      string list * Whitespace.t list list =
   fun strs wss -> function
     | Ident ([ str ], ws) -> (str :: strs, ws :: wss)
     | App { fn; arg = { value = Ident ([ str ], ws); _ }; _ } ->
         go (str :: strs) (ws :: wss) fn.value
     | _ -> fatal Unrecognized_attribute in
  go [] [] tm

(* We define these here so we can refer to them in parsing implicit and nullary applications and in getting patterns.  Note that parentheses are primarily parsed, processed, and printed along with tuples, since their notation overlaps; but are also used as sub-notations in many other notations.  *)

type (_, _, _) identity +=
  | Parens : (closed, No.plus_omega, closed) identity
  | Braces : (closed, No.plus_omega, closed) identity
  | Dot : (closed, No.plus_omega, closed) identity

let parens : (closed, No.plus_omega, closed) notation = (Parens, Outfix)
let braces : (closed, No.plus_omega, closed) notation = (Braces, Outfix)
let dot : (closed, No.plus_omega, closed) notation = (Dot, Outfix)

(* Process a bare identifier, resolving it into either a variable, a cube variable with face, a constant, a numeral, or a degeneracy name (the latter being an error since it isn't applied to anything). *)
let process_ident ctx loc parts =
  let open Monad.Ops (Monad.Maybe) in
  (* A numeral is an ident whose pieces are composed entirely of digits.  Of course if there are more than two parts it's not a *valid* numeral, but we don't allow it as another kind of token either. *)
  if List.is_empty parts then fatal (Anomaly "empty ident")
  else if Lexer.is_numeral parts then
    try { value = Numeral (Q.of_string (String.concat "." parts)); loc }
    with Invalid_argument _ -> fatal (Invalid_numeral (String.concat "." parts))
  else
    match
      match parts with
      | [ x ] ->
          let* _, n = Bwv.find_opt (fun y -> y = Some x) ctx in
          return (Synth (Var (n, None)))
      | [ x; face ] ->
          let* _, v = Bwv.find_opt (fun y -> y = Some x) ctx in
          let* fa = sface_of_string face in
          return (Synth (Var (v, Some fa)))
      | _ -> None
    with
    | Some tm -> { value = tm; loc }
    | None -> (
        match Scope.lookup parts with
        | Some c -> { value = Synth (Const c); loc }
        | None -> (
            match parts with
            | [ str ] when Option.is_some (deg_of_name str) ->
                fatal (Missing_argument_of_degeneracy str)
            | _ -> fatal (Unbound_variable (String.concat "." parts, []))))

let lower_field_name = function
  | [ fld ] when Lexer.valid_field fld && not (Lexer.all_digits fld) -> Some fld
  | _ -> None

let explicit_field_name : type lt ls rt rs.
    (lt, ls, rt, rs) parse located -> string option =
 fun tm ->
  match tm.value with
  | Notn ((Parens, _), n) -> (
      match args n with
      | [ Token (LParen, _); Term { value = Ident (parts, _); _ }; Token (RParen, _) ] ->
          lower_field_name parts
      | _ -> None)
  | _ -> None

(* If an identifier doesn't resolve, we check whether the user might have meant to project one or more fields from a shorter identifier, and give them a hint that field projections require spaces. *)
let rec detect_spaceless_fields ctx loc (bwd_parts : string Bwd.t) fields found =
  match bwd_parts with
  | Emp | Snoc (Emp, _) -> found
  | Snoc (bwd_parts, fld) ->
      Reporter.try_with
        (fun () ->
          let parts = Bwd.to_list bwd_parts in
          let _ = process_ident ctx loc parts in
          detect_spaceless_fields ctx loc bwd_parts (fld :: fields) ((parts, fld :: fields) :: found))
        ~fatal:(fun _ -> detect_spaceless_fields ctx loc bwd_parts (fld :: fields) found)

let reissue_diagnostic message d = fatal_diagnostic (Reporter.with_message d message)

let reissue_unbound_variable ctx loc parts d =
  let alt = detect_spaceless_fields ctx loc (Bwd.of_list parts) [] [] in
  reissue_diagnostic (Reporter.Code.Unbound_variable (String.concat "." parts, alt)) d

let reissue_standalone_field name d =
  reissue_diagnostic (Reporter.Code.Standalone_field_name name) d

let hidden_name_of_field fld pbij = [ ""; fld; String.concat "" pbij ]

let expand_compact_suffix = function
  | [ seg ] when String.length seg > 1 -> List.init (String.length seg) (fun i -> String.make 1 seg.[i])
  | pbij -> pbij

let string_of_higher_field fld pbij =
  let suffix =
    if List.for_all (fun s -> s <> "" && String.length s = 1) pbij then
      String.concat "" pbij
    else String.concat "," pbij
  in
  fld ^ "⟨" ^ suffix ^ "⟩"

let process_higher_field_ident ctx loc fld pbij =
  Reporter.try_with
    (fun () -> process_ident ctx loc (hidden_name_of_field fld pbij))
    ~fatal:(fun ({ message; _ } as d) ->
      match message with
      | Unbound_variable _ -> process_ident ctx loc [ fld; String.concat "" pbij ]
      | _ -> fatal_diagnostic d)

let process_identifier ctx loc parts =
  Reporter.try_with
    (fun () -> process_ident ctx loc parts)
    ~fatal:(fun ({ message; _ } as d) ->
      match message with
      | Unbound_variable _ -> (
          match Scope.resolve_constr parts with
          | Some c -> { value = Raw.Constr ({ value = c; loc }, []); loc }
          | None -> (
              match parts with
              | [ fld ] when Option.is_some (Scope.resolve_field [ fld ]) ->
                  reissue_standalone_field fld d
              | _ -> reissue_unbound_variable ctx loc parts d))
      | _ -> fatal_diagnostic d)

(* Now the master postprocessing function.  Note that this function calls the "process" functions registered for individual notations, but those functions will be defined to call *this* function on their constituents, so we have some "open recursion" going on. *)

let rec process : type n lt ls rt rs.
    (string option, n) Bwv.t -> (lt, ls, rt, rs) parse located -> n check located =
 fun ctx res ->
  let loc = res.loc in
  with_loc loc @@ fun () ->
  match res.value with
  | Notn (n, d) -> (find n).processor ctx (args d) loc
  (* "Application" nodes in result trees are used for anything that syntactically *looks* like an application.  In addition to actual applications of functions, this includes applications of constructors and degeneracy operators, and also field projections.  *)
  | App { fn; arg; _ } -> process_spine ctx fn [ (Wrap arg, res.loc) ]
  | Placeholder _ -> fatal (Unimplemented "unification arguments")
  | Ident (parts, _) -> process_identifier ctx loc parts
  | HigherField (fld, pbij, _) -> process_higher_field_ident ctx loc fld pbij
  | Constr (ident, [], _) -> { value = Raw.Constr ({ value = Constr.intern ident; loc }, []); loc }
  | Constr (_, _, _) -> fatal ?loc (Unimplemented "higher constructors in terms")
  | Field _ -> fatal Parse_error
  | Superscript (Some x, str, _) -> (
      match deg_of_string str.value with
      | Some (Any_deg s) ->
          let body =
            match x.value with
            | Placeholder _ -> None
            | _ -> Some (process ctx x) in
          { value = Synth (Act (str, s, body)); loc }
      | None -> fatal ?loc:str.loc (Invalid_degeneracy str.value))
  | Superscript (None, _, _) -> fatal (Anomaly "degeneracy is head")
  | Hole { li; ri; num; _ } ->
      let hloc = loc <|> Anomaly "missing location in Hole" in
      { value = Hole { scope = ctx; loc = hloc; li = Interval li; ri = Interval ri; num }; loc }

and process_spine : type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (lt, ls, rt, rs) parse located ->
    (wrapped_parse * Asai.Range.t option) list ->
    n check located =
 fun ctx tm args ->
  match tm.value with
  | App { fn; arg; _ } -> process_spine ctx fn ((Wrap arg, tm.loc) :: args)
  | _ -> process_apps ctx tm args

and process_apps : type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (lt, ls, rt, rs) parse located ->
    (wrapped_parse * Asai.Range.t option) list ->
    n check located =
 fun ctx tm args ->
  match process_head ctx tm with
  | `Deg (str, Any_deg s) -> (
      match args with
      | (Wrap arg, loc) :: args ->
          let arg =
            match arg.value with
            | Placeholder _ -> None
            | _ -> Some { value = (process ctx arg).value; loc } in
          process_apply ctx { value = Synth (Act (str, s, arg)); loc } args
      | [] -> fatal ?loc:tm.loc (Anomaly "TODO"))
  | `Constr c ->
      let c = { value = c; loc = tm.loc } in
      let loc = ref None in
      let args =
        List.map
          (fun (Wrap x, l) ->
            loc := l;
            process ctx x)
          args in
      { value = Raw.Constr (c, args); loc = !loc }
  | `Fn fn -> process_apply ctx fn args

and process_head : type n lt ls rt rs.
    (string option, n) Bwv.t ->
    (lt, ls, rt, rs) parse located ->
    [ `Deg of string located * any_deg | `Constr of Constr.t | `Fn of n check located ] =
 fun ctx tm ->
 match tm.value with
  | Constr (ident, [], _) -> `Constr (Constr.intern ident)
  | Constr (_, _, _) -> fatal ?loc:tm.loc (Unimplemented "higher constructors in terms")
  | HigherField (fld, pbij, _) ->
      `Fn (process_higher_field_ident ctx tm.loc fld pbij)
  | Ident ([ str ], _) -> (
      match deg_of_name str with
      | Some s -> `Deg (locate_opt tm.loc str, s)
      | None -> (
          match process_identifier ctx tm.loc [ str ] with
          | { value = Raw.Constr ({ value = c; _ }, []); _ } -> `Constr c
          | fn -> `Fn fn))
  | Ident (parts, _) -> (
      match process_identifier ctx tm.loc parts with
      | { value = Raw.Constr ({ value = c; _ }, []); _ } -> `Constr c
      | fn -> `Fn fn)
  | _ -> `Fn (process ctx tm)

and process_apply : type n.
    (string option, n) Bwv.t ->
    n check located ->
    (wrapped_parse * Asai.Range.t option) list ->
    n check located =
 fun ctx fn fnargs ->
  let field_projection loc fld args =
    let fn =
      match fn.value with
      | Synth sfn -> { value = sfn; loc = fn.loc }
      | _ -> fatal (Nonsynthesizing "head of field application") in
    process_apply ctx { value = Synth (Field (fn, `Name (fld, []))); loc } args in
  let apply_explicit_arg loc arg args =
    process_apply ctx
      {
        value = Synth (App (fn, locate_opt arg.loc (Some arg.value), locate_opt arg.loc `Explicit));
        loc;
      }
      args in
  match fnargs with
  | [] -> fn
  | (Wrap { value = HigherField (fld, pbij, _); _ }, loc) :: args -> (
      let higher_ident =
        Reporter.try_with
          (fun () -> Some (process_higher_field_ident ctx loc fld pbij))
          ~fatal:(fun _ -> None)
      in
      match higher_ident with
      | Some arg -> apply_explicit_arg loc arg args
      | None -> (
          try
            let fld = `Name (fld, List.map int_of_string (expand_compact_suffix pbij)) in
            let fn =
              match fn.value with
              | Synth sfn -> { value = sfn; loc = fn.loc }
              | _ -> fatal (Nonsynthesizing "head of field application") in
            process_apply ctx { value = Synth (Field (fn, fld)); loc } args
          with Failure _ -> fatal (Invalid_field (string_of_higher_field fld pbij))))
  | (Wrap { value = Field (fld, pbij, _); _ }, loc) :: args -> (
      let higher_ident =
        if pbij <> [] && not (Lexer.all_digits fld) then
          Reporter.try_with
            (fun () -> Some (process_higher_field_ident ctx loc fld pbij))
            ~fatal:(fun _ -> None)
        else None in
      match higher_ident with
      | Some arg -> apply_explicit_arg loc arg args
      | None -> (
          try
            let fld =
              match int_of_string_opt fld with
              | Some n -> `Int n
              | None -> `Name (fld, List.map int_of_string pbij) in
            let fn =
              match fn.value with
              | Synth sfn -> { value = sfn; loc = fn.loc }
              | _ -> fatal (Nonsynthesizing "head of field application") in
            process_apply ctx { value = Synth (Field (fn, fld)); loc } args
          with Failure _ -> fatal (Invalid_field (string_of_higher_field fld pbij))))
  | (Wrap { value = Notn ((Dot, _), _); loc = dotloc }, _) :: (Wrap arg, loc) :: rest -> (
      match explicit_field_name arg with
      | Some fld -> field_projection loc fld rest
      | None ->
          process_apply ctx
            { value = Synth (App (fn, locate_opt dotloc None, locate_opt None `Explicit)); loc }
            ((Wrap arg, loc) :: rest))
  | (Wrap { value = Notn ((Braces, _), n); loc = braceloc }, loc) :: rest -> (
      match args n with
      | [ Token (LBrace, _); Term arg; Token (RBrace, _) ] ->
          let arg = process ctx arg in
          process_apply ctx
            {
              value =
                Synth (App (fn, locate_opt arg.loc (Some arg.value), locate_opt braceloc `Implicit));
              loc;
            }
            rest
      | _ -> fatal (Anomaly "invalid notation arguments for braces"))
  | (Wrap { value = Notn ((Dot, _), _); loc = dotloc }, loc) :: rest ->
      process_apply ctx
        { value = Synth (App (fn, locate_opt dotloc None, locate_opt None `Explicit)); loc }
        rest
  | (Wrap { value = Ident ([ fld ], _); loc = argloc }, loc) :: args -> (
      Reporter.try_with
        (fun () ->
          let arg = process_ident ctx argloc [ fld ] in
          apply_explicit_arg loc arg args)
        ~fatal:(fun ({ message; _ } as d) ->
          match message with
          | Unbound_variable _ -> (
              match Scope.resolve_constr [ fld ] with
              | Some c ->
                  let arg = { value = Raw.Constr ({ value = c; loc = argloc }, []); loc = argloc } in
                  apply_explicit_arg loc arg args
              | None -> (
                  if Option.is_some (Scope.resolve_field [ fld ])
                     || (Lexer.valid_field fld && not (Lexer.all_digits fld))
                  then field_projection loc fld args
                  else reissue_unbound_variable ctx argloc [ fld ] d))
          | _ -> fatal_diagnostic d))
  | (Wrap arg, loc) :: args ->
      let arg = process ctx arg in
      apply_explicit_arg loc arg args

and process_synth : type n lt ls rt rs.
    (string option, n) Bwv.t -> (lt, ls, rt, rs) parse located -> string -> n synth located =
 fun ctx x str ->
  match process ctx x with
  | { value = Synth value; loc } -> { value; loc }
  | { loc; _ } -> fatal ?loc (Nonsynthesizing str)

type _ processed_tel =
  | Processed_tel :
      ('n, 'k, 'nk) Raw.tel * (string option, 'nk) Bwv.t * (Whitespace.t list, 'k) Vec.t
      -> 'n processed_tel

let rec process_tel : type n. (string option, n) Bwv.t -> Parameter.t list -> n processed_tel =
 fun ctx parameters ->
  match parameters with
  | [] -> Processed_tel (Emp, ctx, [])
  | { names; ty; _ } :: parameters -> process_vars ctx names ty parameters

and process_vars : type n.
    (string option, n) Bwv.t ->
    (string option * Whitespace.t list) list ->
    wrapped_parse ->
    Parameter.t list ->
    n processed_tel =
 fun ctx names (Wrap ty) parameters ->
  match names with
  | [] -> process_tel ctx parameters
  | (name, w) :: names ->
      let pty = process ctx ty in
      let (Processed_tel (tel, ctx, ws)) =
        process_vars (Bwv.snoc ctx name) names (Wrap ty) parameters in
      Processed_tel (Ext (name, pty, tel), ctx, w :: ws)

let get_pattern : type lt1 ls1 rt1 rs1. (lt1, ls1, rt1, rs1) parse located -> Matchpattern.t =
 fun pat ->
  let rec go : type n lt1 ls1 rt1 rs1.
      (lt1, ls1, rt1, rs1) parse located -> (Matchpattern.t, n) Vec.t located -> Matchpattern.t =
   fun pat pats ->
    match pat.value with
    | Ident (xs, _) -> (
        match Scope.resolve_constr xs with
        | Some c -> Constr (locate_opt pat.loc c, pats.value)
        | None -> (
            match xs with
            | [ x ] when Lexer.valid_var x -> (
                match pats.value with
                | [] -> Var (locate_opt pat.loc (Some x))
                | _ -> fatal ?loc:pat.loc Parse_error)
            | _ -> fatal ?loc:pat.loc (Invalid_variable xs)))
    | Placeholder _ -> (
        match pats.value with
        | [] -> Var (locate_opt pat.loc None)
        | _ -> fatal ?loc:pat.loc Parse_error)
    | Constr (c, [], _) -> Constr (locate_opt pat.loc (Constr.intern c), pats.value)
    | Constr (_, _, _) ->
        fatal ?loc:pat.loc (Unimplemented "higher constructors in match patterns")
    | App { fn; arg; _ } ->
        go fn
          (locate_opt pats.loc
             (go arg (locate_opt arg.loc Vec.[]) :: pats.value : (Matchpattern.t, n Fwn.suc) Vec.t))
    | Notn (notn, n) -> pattern notn (args n) pat.loc
    | _ -> fatal ?loc:pat.loc Parse_error in
  go pat (locate_opt pat.loc Vec.[])

(* Now that we've defined these functions, we can pass them back to User. *)
let () = User.global_processor := { process = (fun ctx x -> process ctx x); pattern = get_pattern }
