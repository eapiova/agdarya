open Util
open Core
open Reporter
open Notation
open PPrint
open Print
module StringMap = Map.Make (String)

(* A user notation pattern is a nonempty sequence of operator symbols and variable names.  There must be at least one operator symbol, and any two variable names must be separated by at least one symbol.  It is left-closed if the first element is an operator symbol and left-open if the first element is a variable, and similarly for right-open and -closed and the last element.  The two opennesses in turn determine whether it is infix, prefix, postfix, or outfix, but not its associativity or tightness.  *)

module Pattern = struct
  (* This type ensures statically that all the invariants mentioned above must hold, and is parametrized by the left- and right-openness.
     Each symbol or variable is stored along with the type of space following it, except for those that occur last. *)
  type (_, _) t =
    | Op_nil : Token.t * Whitespace.t list -> (closed, closed) t
    (* If a pattern ends with a variable, that variable must be immediately preceded by an operator symbol, so we include that in the corresponding "nil". *)
    | Var_nil :
        (Token.t * space * Whitespace.t list) * (string * Whitespace.t list)
        -> (closed, 's opn) t
    | Binder_nil :
        (Token.t * space * Whitespace.t list) * (string * Whitespace.t list)
        -> (closed, 's opn) t
    | Op : (Token.t * space * Whitespace.t list) * ('left, 'right) t -> (closed, 'right) t
    | Var : (string * space * Whitespace.t list) * (closed, 'right) t -> ('s opn, 'right) t
    | Binder : (string * space * Whitespace.t list) * (closed, 'right) t -> ('s opn, 'right) t

  type atom = [ `Op of Token.t | `Var of string | `Binder of string ]

  (* List the variable names used in a pattern. *)
  let rec vars : type left right. (left, right) t -> string list = function
    | Op_nil _ -> []
    | Var_nil (_, (x, _)) -> [ x ]
    | Binder_nil (_, (x, _)) -> [ x ]
    | Op (_, pat) -> vars pat
    | Var ((x, _, _), pat) -> x :: vars pat
    | Binder ((x, _, _), pat) -> x :: vars pat

  let rec value_vars : type left right. (left, right) t -> string list = function
    | Op_nil _ -> []
    | Var_nil (_, (x, _)) -> [ x ]
    | Binder_nil _ -> []
    | Op (_, pat) -> value_vars pat
    | Var ((x, _, _), pat) -> x :: value_vars pat
    | Binder (_, pat) -> value_vars pat

  let rec atoms : type left right. (left, right) t -> atom list = function
    | Op_nil (tok, _) -> [ `Op tok ]
    | Var_nil ((tok, _, _), (x, _)) -> [ `Op tok; `Var x ]
    | Binder_nil ((tok, _, _), (x, _)) -> [ `Op tok; `Binder x ]
    | Op ((tok, _, _), pat) -> `Op tok :: atoms pat
    | Var ((x, _, _), pat) -> `Var x :: atoms pat
    | Binder ((x, _, _), pat) -> `Binder x :: atoms pat

  let inner_symbols : type left right.
      (left, right) t ->
      [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ] =
   fun pat ->
    let rec go : type left right. (left, right) t -> Token.t option list * Token.t = function
      | Op_nil (tok, _) -> ([], tok)
      | Var_nil ((tok, _, _), _) -> ([], tok)
      | Binder_nil ((tok, _, _), _) -> ([], tok)
      | Op ((tok, _, _), pat) ->
          let inner, last = go pat in
          (Some tok :: inner, last)
      | Var (_, pat) ->
          let inner, last = go pat in
          (None :: inner, last)
      | Binder (_, pat) ->
          let inner, last = go pat in
          (None :: inner, last) in
    match go pat with
    | Some first :: inner, last -> `Multiple (first, inner, last)
    | None :: Some first :: inner, last -> `Multiple (first, inner, last)
    | None :: None :: _, _ -> fatal (Anomaly "two sequential variables in inner_symbols")
    | [ None ], tok | [], tok -> `Single tok

  (* A pattern parametrized only by its right-openness. *)
  type _ right_t = Right : ('left, 'right) t -> 'right right_t

  (* Cons a variable on the left of any pattern, raising an error if that would put two variables next to each other. *)
  let var : type left right s.
      string * space * Whitespace.t list -> (left, right) t -> (s opn, right) t =
   fun v pat ->
    match pat with
    | Op_nil _ as pat -> Var (v, pat)
    | Var_nil _ as pat -> Var (v, pat)
    | Binder_nil _ as pat -> Var (v, pat)
    | Op (_, _) as pat -> Var (v, pat)
    | _ -> fatal (Invalid_notation_pattern "missing symbol between variables")

  let binder : type left right s.
      string * space * Whitespace.t list -> (left, right) t -> (s opn, right) t =
   fun v pat ->
    match pat with
    | Op_nil _ as pat -> Binder (v, pat)
    | Var_nil _ as pat -> Binder (v, pat)
    | Binder_nil _ as pat -> Binder (v, pat)
    | Op (_, _) as pat -> Binder (v, pat)
    | _ -> fatal (Invalid_notation_pattern "missing symbol between variables")

  let rec to_string : type left right. (left, right) t -> string = function
    | Op_nil (tok, _) -> Token.to_string tok
    | Var_nil ((tok, _, _), _) -> Token.to_string tok ^ " _"
    | Binder_nil ((tok, _, _), _) -> Token.to_string tok ^ " _"
    | Op ((tok, _, _), rest) -> Token.to_string tok ^ " " ^ to_string rest
    | Var (_, rest) -> "_ " ^ to_string rest
    | Binder (_, rest) -> "_ " ^ to_string rest
end

(* Print a *pattern* the way the user would enter it in a "notation" command, with quotes around the operator symbols. *)
let pp_pattern : type left right. (left, right) Pattern.t -> document * Whitespace.t list =
 fun pattern ->
  let rec go : type left right.
      (left, right) Pattern.t -> Whitespace.t list option -> document * Whitespace.t list =
   fun pattern prews ->
    match pattern with
    | Var ((x, _, ws), pat) ->
        let ppat, wpat = go pat (Some ws) in
        (group (optional (pp_ws `Break) prews ^^ utf8string x) ^^ ppat, wpat)
    | Binder ((x, _, ws), pat) ->
        let ppat, wpat = go pat (Some ws) in
        ( group (optional (pp_ws `Break) prews ^^ Token.pp LBracket ^^ utf8string x ^^ Token.pp RBracket)
          ^^ ppat,
          wpat )
    | Var_nil ((op, _, opws), (x, varws)) ->
        ( group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op))
          ^^ group (pp_ws `Break opws ^^ utf8string x),
          varws )
    | Binder_nil ((op, _, opws), (x, varws)) ->
        ( group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op))
          ^^ group
               (pp_ws `Break opws ^^ Token.pp LBracket ^^ utf8string x ^^ Token.pp RBracket),
          varws )
    | Op ((op, _, ws), pat) ->
        let ppat, wpat = go pat (Some ws) in
        (group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op)) ^^ ppat, wpat)
    | Op_nil (op, ws) -> (group (optional (pp_ws `Break) prews ^^ dquotes (Token.pp op)), ws) in
  go pattern None

type binder_slot = {
  prefix_tokens : Token.t list;
  binder_var : string;
  dom_var : string;
}

type binder_info = {
  slots : binder_slot list;
  body_prefix_tokens : Token.t list;
  body_var : string;
}

(* A user "prenotation" includes all the information from a "notation" command, parsed and validated into a pattern, fixity, and so on, but not yet compiled into a notation tree. *)

type key = [ `Constant of Core.Constant.t | `Constr of Core.Constr.t * int ]

type ('left, 'tight, 'right) prenotation_data = {
  name : string;
  fixity : ('left, 'tight, 'right) fixity;
  pattern : ('left, 'right) Pattern.t;
  key : key;
  binder : binder_info option;
  val_vars : string list;
}

type prenotation = User : ('left, 'tight, 'right) prenotation_data -> prenotation

(* Whereas a user "notation" has been compiled into a notation tree, but remembers the variables from the pattern and the definition, so as to implement the necessary permutation. *)

type notation = {
  keys : key list;
  notn : Notation.t;
  binder : binder_info option;
  pat_vars : string list;
  val_vars : string list;
  inner_symbols : [ `Single of Token.t | `Multiple of Token.t * Token.t option list * Token.t ];
}

(* The global processing function isn't defined until postprocess.ml, but we need it before that here. *)

type global_processor = {
  process :
    'n 'lt 'ls 'rt 'rs.
    (string option, 'n) Bwv.t ->
    ('lt, 'ls, 'rt, 'rs) parse Asai.Range.located ->
    'n Raw.check Asai.Range.located;
  pattern : 'lt 'ls 'rt 'rs. ('lt, 'ls, 'rt, 'rs) parse Asai.Range.located -> Matchpattern.t;
}

let global_processor : global_processor ref =
  ref
    {
      process = (fun _ _ -> fatal (Anomaly "global_processor not set"));
      pattern = (fun _ -> fatal (Anomaly "global_processor not set"));
    }

let rec binder_var_spine : type lt ls rt rs.
    (lt, ls, rt, rs) parse Asai.Range.located -> string option Asai.Range.located list = function
  | { value = App { fn; arg; _ }; _ } -> binder_var_spine fn @ [ binder_var arg ]
  | tm -> [ binder_var tm ]

and binder_var : type lt ls rt rs.
    (lt, ls, rt, rs) parse Asai.Range.located -> string option Asai.Range.located =
 fun { value; loc } ->
  match value with
  | Ident ([ x ], _) when Lexer.valid_var x -> Asai.Range.locate_opt loc (Some x)
  | Placeholder _ -> Asai.Range.locate_opt loc None
  | Ident (xs, _) -> fatal ?loc (Invalid_variable xs)
  | _ -> fatal ?loc Parse_error

let weaken_check ({ value; loc } : _ Asai.Range.located) = Asai.Range.locate_opt loc (Raw.Weaken (value, Eq))

let binder_start_token ({ slots; _ } : binder_info) =
  match slots with
  | { prefix_tokens = tok :: _; _ } :: _ -> tok
  | _ -> fatal (Anomaly "binder notation missing start token")

type binder_slot_use = { vars : wrapped_parse; dom : wrapped_parse }
type binder_use = { slots : binder_slot_use list; body : wrapped_parse }

let binder_use_of_observations (binder : binder_info) (obs : observation list) : binder_use option =
  let open Monad.Ops (Monad.Maybe) in
  let expect_token tok = function
    | Token (tok', _) :: obs when tok = tok' -> Some obs
    | _ -> None
  in
  let rec expect_tokens toks obs =
    match toks with
    | [] -> Some obs
    | tok :: toks ->
        let* obs = expect_token tok obs in
        expect_tokens toks obs
  in
  let expect_term = function
    | Term tm :: obs -> Some ((Wrap tm : wrapped_parse), obs)
    | _ -> None
  in
  let rec after_prefix :
      binder_slot -> binder_slot list -> observation list -> binder_slot_use list -> binder_use option =
   fun _slot rest obs accum ->
    let* vars, obs = expect_term obs in
    let* obs = expect_token Colon obs in
    let* dom, obs = expect_term obs in
    match rest with
    | next :: rest ->
        let* obs = expect_tokens next.prefix_tokens obs in
        after_prefix next rest obs ({ vars; dom } :: accum)
    | [] ->
        let* obs = expect_tokens binder.body_prefix_tokens obs in
        let* body, obs = expect_term obs in
        let* () =
          match obs with
          | [] -> Some ()
          | _ :: _ -> None
        in
        Some { slots = List.rev ({ vars; dom } :: accum); body }
  in
  match binder.slots with
  | [] -> None
  | first :: rest ->
      let* obs = expect_tokens first.prefix_tokens obs in
      after_prefix first rest obs []

type any_check_builder = { build : 'n. (string option, 'n) Bwv.t -> 'n Raw.check Asai.Range.located }

let rec abstract_builder : type n.
    (string option, n) Bwv.t ->
    string option Asai.Range.located list ->
    any_check_builder ->
    n Raw.check Asai.Range.located =
 fun ctx vars builder ->
  match vars with
  | [] -> builder.build ctx
  | x :: xs ->
      let body = abstract_builder (Bwv.snoc ctx x.value) xs builder in
      let lam_loc = Range.merge_opt x.loc body.loc in
      Asai.Range.locate_opt lam_loc
        (Raw.Lam
           { name = x; cube = Asai.Range.locate_opt None `Normal; implicit = `Explicit; dom = None; body })

(* Compile a prenotation into a notation.  *)

let make_user : prenotation -> notation =
 fun notn ->
  let open Notation in
  let (User (type l t r)
        ({ name; fixity; pattern; key; binder; val_vars } : (l, t, r) prenotation_data)) =
    notn in
  let module New = Make (struct
    type nonrec left = l
    type nonrec tight = t
    type nonrec right = r
  end) in
  let n = (New.User, fixity) in
  let pat_vars = Pattern.vars pattern in
  let inner_symbols = Pattern.inner_symbols pattern in
  make n
    {
      name;
      (* Convert a user notation pattern to a notation tree.  Note that our highly structured definition of the type of patterns, that enforces invariants statically, means that this function CANNOT FAIL. *)
      tree =
        (* We have to handle the beginning specially, since the start and end of a notation tree are different depending on whether it is left-open or left-closed.  So we have an internal recursive function that handles everything except the first operator symbol. *)
        (let rec go : type left l tight.
             (l, r) Pattern.t -> (tight, left) tree -> (tight, left) tree =
          fun pat n ->
           match pat with
           | Op_nil (tok, _) -> op tok n
           | Var_nil ((tok, _, _), _) -> op tok n
           | Binder_nil ((tok, _, _), _) -> op tok n
           | Op ((tok, _, _), pat) -> op tok (go pat n)
           | Var (_, Op ((tok, _, _), pat)) -> term tok (go pat n)
           | Var (_, Op_nil (tok, _)) -> term tok n
           | Var (_, Var_nil ((tok, _, _), _)) -> term tok n
           | Var (_, Binder_nil ((tok, _, _), _)) -> term tok n
           | Binder (_, Op ((tok, _, _), pat)) -> term tok (go pat n)
           | Binder (_, Op_nil (tok, _)) -> term tok n
           | Binder (_, Var_nil ((tok, _, _), _)) -> term tok n
           | Binder (_, Binder_nil ((tok, _, _), _)) -> term tok n in
         match pattern with
         | Op_nil (tok, _) -> Closed_entry (eop tok (Done_closed n))
         | Var (_, Op ((tok, _, _), pat)) -> Open_entry (eop tok (go pat (done_open n)))
         | Var (_, Op_nil (tok, _)) -> Open_entry (eop tok (done_open n))
         | Var (_, Var_nil ((tok, _, _), _)) -> Open_entry (eop tok (done_open n))
         | Var (_, Binder_nil ((tok, _, _), _)) -> Open_entry (eop tok (done_open n))
         | Binder (_, Op ((tok, _, _), pat)) -> Open_entry (eop tok (go pat (done_open n)))
         | Binder (_, Op_nil (tok, _)) -> Open_entry (eop tok (done_open n))
         | Binder (_, Var_nil ((tok, _, _), _)) -> Open_entry (eop tok (done_open n))
         | Binder (_, Binder_nil ((tok, _, _), _)) -> Open_entry (eop tok (done_open n))
         | Op ((tok, _, _), pat) -> Closed_entry (eop tok (go pat (Done_closed n)))
         | Var_nil ((tok, _, _), _) -> Closed_entry (eop tok (Done_closed n))
         | Binder_nil ((tok, _, _), _) -> Closed_entry (eop tok (Done_closed n)));
      processor =
        (match binder with
         | Some binder -> (
             match key with
             | `Constr _ ->
                 (fun _ _ loc ->
                   fatal ?loc
                     (Invalid_notation_pattern
                        "binder notations currently require a constant head"))
             | `Constant c ->
                 fun ctx obs loc ->
                   let apply args loc =
                     let spine =
                       List.fold_left
                         (fun acc k ->
                           match StringMap.find_opt k args with
                           | None -> fatal (Anomaly "missing argument processing binder notation")
                           | Some ({ value = arg; loc = argloc } : _ Asai.Range.located) ->
                               Raw.App
                                 ( Asai.Range.locate_opt loc (Raw.Synth acc),
                                   Asai.Range.locate_opt argloc (Some arg),
                                   Asai.Range.locate_opt None `Explicit ))
                         (Const c) val_vars in
                     Asai.Range.locate_opt loc (Raw.Synth spine)
                   in
                    let rec build :
                        type n lt ls rt rs.
                        (string option, n) Bwv.t ->
                        string option Asai.Range.located list ->
                        n Raw.check Asai.Range.located ->
                        (lt, ls, rt, rs) parse Asai.Range.located ->
                        n Raw.check Asai.Range.located =
                     fun ctx vars dom body ->
                      match vars with
                      | [] -> (!global_processor.process ctx body : n Raw.check Asai.Range.located)
                      | x :: xs ->
                          let body = build (Bwv.snoc ctx x.value) xs (weaken_check dom) body in
                          let lam_loc = Range.merge_opt x.loc body.loc in
                          let lam =
                            Asai.Range.locate_opt lam_loc
                              (Raw.Lam
                                 {
                                   name = x;
                                   cube = Asai.Range.locate_opt None `Normal;
                                   implicit = `Explicit;
                                   dom = None;
                                   body;
                                 })
                          in
                          apply
                            (StringMap.empty
                            |> StringMap.add
                                 (match binder.slots with
                                 | [ { dom_var; _ } ] -> dom_var
                                 | _ ->
                                     fatal
                                       (Anomaly
                                          "single-slot binder build used for multi-slot binder"))
                                 dom
                            |> StringMap.add binder.body_var lam)
                            (Range.merge_opt dom.loc lam.loc)
                    in
                    match binder_use_of_observations binder obs with
                    | Some { slots = [ { vars = Wrap vars; dom = Wrap dom } ]; body = Wrap body } ->
                        let vars = binder_var_spine vars in
                        let dom = !global_processor.process ctx dom in
                        build ctx vars dom body
                    | Some { slots = slot_uses; body = Wrap body } ->
                        let body_vars =
                          List.concat_map
                            (fun { vars = Wrap vars; _ } -> binder_var_spine vars)
                            slot_uses
                        in
                        let _, args =
                          List.fold_left2
                            (fun (prev_vars, args) slot { vars = Wrap vars; dom = Wrap dom } ->
                              let dom =
                                abstract_builder ctx prev_vars
                                  { build = (fun ctx -> !global_processor.process ctx dom) }
                              in
                              let slot_vars = binder_var_spine vars in
                              ( prev_vars @ slot_vars,
                                args |> StringMap.add slot.dom_var dom ))
                            ([], StringMap.empty)
                            binder.slots slot_uses
                        in
                        let body =
                          abstract_builder ctx body_vars
                            { build = (fun ctx -> !global_processor.process ctx body) }
                        in
                        apply (args |> StringMap.add binder.body_var body) loc
                    | None ->
                        fatal ?loc
                          (Anomaly ("invalid notation arguments for user binder notation: " ^ name)))
         | None ->
             fun ctx obs loc ->
               let args =
                 List.fold_left2
                   (fun acc k -> function
                     | (Wrap x : wrapped_parse) ->
                         acc |> StringMap.add k (!global_processor.process ctx x))
                   StringMap.empty pat_vars
                   (List.filter_map
                      (function
                        | Term x -> Some (Wrap x : wrapped_parse)
                        | _ -> None)
                      obs) in
               let value =
                 match key with
                 | `Constant c ->
                     let spine =
                       List.fold_left
                         (fun acc k ->
                           match StringMap.find_opt k args with
                           | None -> fatal (Anomaly "not found processing user")
                           | Some ({ value = arg; loc = argloc } : _ Asai.Range.located) ->
                               Raw.App
                                 ( Asai.Range.locate_opt loc (Raw.Synth acc),
                                   Asai.Range.locate_opt argloc (Some arg),
                                   Asai.Range.locate_opt None `Explicit ))
                         (Const c) val_vars in
                     Raw.Synth spine
                 | `Constr (c, _) ->
                     let args = List.map (fun k -> StringMap.find k args) val_vars in
                     Raw.Constr (Asai.Range.locate_opt loc c, args) in
               Asai.Range.locate_opt loc value);
      pattern =
        (match binder with
         | Some _ ->
             (fun _ loc ->
               fatal ?loc
                 (Invalid_notation_pattern "binder-aware notations are not available in patterns"))
         | None ->
             fun obs loc ->
               let open Mlist.Monadic (Monad.State (struct
                 type t = Matchpattern.t StringMap.t
               end)) in
               let (), args =
                 miterM
                   (fun [ k; (Wrap x : wrapped_parse) ] acc ->
                     ((), acc |> StringMap.add k (!global_processor.pattern x)))
                   [
                     pat_vars;
                     List.filter_map
                       (function
                         | Term x -> Some (Wrap x : wrapped_parse)
                         | _ -> None)
                       obs;
                   ]
                   StringMap.empty in
               match key with
               | `Constr (c, _) ->
                   let (Wrap args) = Vec.of_list_map (fun k -> StringMap.find k args) val_vars in
                   Matchpattern.Constr (Asai.Range.locate_opt loc c, args)
               | _ -> fatal (Anomaly "TODO"));
      (* We define this function inline here so that it can match against the constructor New.User that was generated above by the inline Make functor application.  The only way I can think of to factor this function out (and, for instance, put it in user.ml instead of this file) would be to pass it a first-class module as an argument.  At the moment, that seems like unnecessary complication. *)
      print_term =
        Some
          (match binder with
           | Some binder ->
               (fun obs ->
                 let compact_term tm =
                   let doc, _ = pp_term tm in
                   let buf = Buffer.create 32 in
                   PPrint.ToBuffer.compact buf doc;
                   Buffer.contents buf
                 in
                 let pp_wrapped (Wrap tm : wrapped_parse) = pp_term tm in
                 let pp_prefix_tokens = function
                   | [] -> fatal (Anomaly "binder notation missing prefix tokens")
                   | tok :: toks ->
                       List.fold_left
                         (fun acc tok -> acc ^^ PPrint.blank 1 ^^ Token.pp tok)
                         (Token.pp tok) toks
                 in
                 let pp_between_tokens = function
                   | [] -> PPrint.empty
                   | tok :: toks when tok = Token.Op "," ->
                       List.fold_left
                         (fun acc tok -> acc ^^ PPrint.blank 1 ^^ Token.pp tok)
                         (Token.pp tok) toks
                   | tok :: toks ->
                       PPrint.blank 1
                       ^^ List.fold_left
                            (fun acc tok -> acc ^^ PPrint.blank 1 ^^ Token.pp tok)
                            (Token.pp tok) toks
                 in
                 let pp_vars vars =
                   List.fold_left
                     (fun acc tm ->
                       let doc, _ = pp_wrapped tm in
                       if acc = PPrint.empty then doc else acc ^^ PPrint.blank 1 ^^ doc)
                     PPrint.empty vars
                 in
                 let pp_slot vars dom =
                   let vars_doc = pp_vars vars in
                   let dom_doc, _ = pp_wrapped dom in
                   vars_doc ^^ PPrint.blank 1 ^^ Token.pp Colon ^^ PPrint.blank 1 ^^ dom_doc
                 in
                 let rec collect (Wrap ({ value; _ } as tm) : wrapped_parse) :
                     (wrapped_parse * wrapped_parse) list * wrapped_parse =
                   match value with
                   | Notn ((New.User, _), d) -> (
                       match binder_use_of_observations binder (args d) with
                       | Some { slots = [ { vars; dom } ]; body } ->
                           let rest, body = collect body in
                           ((vars, dom) :: rest, body)
                       | Some _ | None -> ([], (Wrap tm : wrapped_parse)))
                   | _ -> ([], (Wrap tm : wrapped_parse))
                 in
                 let group_clauses clauses =
                   let rec go current_vars current_dom current_key acc = function
                     | [] ->
                         List.rev ((List.rev current_vars, current_dom) :: acc)
                     | (vars, dom) :: rest ->
                         let (Wrap dom_tm : wrapped_parse) = dom in
                         let key = compact_term dom_tm in
                         if key = current_key then go (vars :: current_vars) current_dom current_key acc rest
                         else
                           go [ vars ] dom key ((List.rev current_vars, current_dom) :: acc) rest
                   in
                   match clauses with
                   | [] -> []
                   | (vars, dom) :: rest ->
                       let (Wrap dom_tm : wrapped_parse) = dom in
                       go [ vars ] dom (compact_term dom_tm) [] rest
                 in
                 match binder_use_of_observations binder obs with
                 | Some { slots = [ { vars; dom } ]; body }
                   when binder.body_prefix_tokens = [ Token.Op "," ] -> (
                     let clauses, final_body = collect body in
                     let clauses = group_clauses ((vars, dom) :: clauses) in
                     let slot =
                       match binder.slots with
                       | [ slot ] -> slot
                       | _ -> fatal (Anomaly "comma binder chain used for multi-slot binder")
                     in
                     let clauses_doc =
                       match clauses with
                       | [] -> fatal (Anomaly "missing binder clauses")
                       | (vars, dom) :: clauses ->
                           List.fold_left
                             (fun acc (vars, dom) ->
                               acc
                               ^^ pp_between_tokens binder.body_prefix_tokens
                               ^^ PPrint.blank 1
                               ^^ pp_slot vars dom)
                             (pp_prefix_tokens slot.prefix_tokens
                             ^^ PPrint.blank 1
                             ^^ pp_slot vars dom)
                             clauses
                     in
                     let body_doc, body_ws = pp_wrapped final_body in
                     ( align
                         (group
                            (clauses_doc
                            ^^ pp_between_tokens binder.body_prefix_tokens
                            ^^ PPrint.blank 1
                            ^^ body_doc)),
                       body_ws ))
                 | Some { slots = slot_uses; body } -> (
                     match (binder.slots, slot_uses) with
                     | first_slot :: rest_slots, first_use :: rest_uses ->
                         let first_doc =
                           pp_prefix_tokens first_slot.prefix_tokens
                           ^^ PPrint.blank 1
                           ^^ pp_slot [ first_use.vars ] first_use.dom
                         in
                         let doc =
                           List.fold_left2
                             (fun acc slot slot_use ->
                               acc
                               ^^ pp_between_tokens slot.prefix_tokens
                               ^^ PPrint.blank 1
                               ^^ pp_slot [ slot_use.vars ] slot_use.dom)
                             first_doc rest_slots rest_uses
                         in
                         let body_doc, body_ws = pp_wrapped body in
                         ( align
                             (group
                                (doc
                                ^^ pp_between_tokens binder.body_prefix_tokens
                                ^^ PPrint.blank 1
                                ^^ body_doc)),
                           body_ws )
                     | _ ->
                         fatal (Anomaly ("invalid binder notation arguments for " ^ name)))
                 | None -> fatal (Anomaly ("invalid notation arguments for user binder notation: " ^ name)))
           | None ->
               (fun obs ->
                 let rec go : type l r.
                     bool -> (l, r) Pattern.t -> observation list -> document * Whitespace.t list =
                  fun first pat obs ->
                   match (pat, obs) with
                   | Op ((op, br, _), pat), Token (op', (wsop, _)) :: obs when op = op' ->
                       let rest, ws = go false pat obs in
                       (Token.pp op ^^ pp_ws br wsop ^^ rest, ws)
                   | Op_nil (op, _), [ Token (op', (wsop, _)) ] when op = op' -> (Token.pp op, wsop)
                   | Var_nil ((op, opbr, _), _), [ Token (op', (wsop, _)); Term x ] when op = op' ->
                       let xdoc, xws =
                         match x.value with
                         | Notn ((New.User, _), d) -> go false pattern (args d)
                         | _ -> pp_term x in
                       (Token.pp op ^^ pp_ws opbr wsop ^^ xdoc, xws)
                   | Binder_nil ((op, opbr, _), _), [ Token (op', (wsop, _)); Term x ]
                     when op = op' ->
                       let xdoc, xws =
                         match x.value with
                         | Notn ((New.User, _), d) -> go false pattern (args d)
                         | _ -> pp_term x in
                       (Token.pp op ^^ pp_ws opbr wsop ^^ xdoc, xws)
                   | Var ((_, br, _), pat), Term x :: obs ->
                       let xdoc, xws =
                         match (first, x.value) with
                         | true, Notn ((New.User, _), d) -> go true pattern (args d)
                         | _ -> pp_term x in
                       let rest, ws = go false pat obs in
                       (xdoc ^^ pp_ws br xws ^^ rest, ws)
                   | Binder ((_, br, _), pat), Term x :: obs ->
                       let xdoc, xws =
                         match (first, x.value) with
                         | true, Notn ((New.User, _), d) -> go true pattern (args d)
                         | _ -> pp_term x in
                       let rest, ws = go false pat obs in
                       (xdoc ^^ pp_ws br xws ^^ rest, ws)
                   | _ -> fatal (Anomaly ("invalid notation arguments for user notation: " ^ name))
                 in
                 let doc, ws = go true pattern obs in
                 (align (group doc), ws)));
      print_case = None;
      is_case = (fun _ -> false);
    };
  { keys = [ key ]; notn = Wrap n; binder; pat_vars; val_vars; inner_symbols }
