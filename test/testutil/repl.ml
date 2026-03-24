open Util
open Tbwd
open Dim
open Core
open Origin
open Readback
open Reporter
open Parser
open Unparse
open Print
open Norm
open Check
open Term
open Value
open Raw
open Asai.Range

type any_dataconstrs =
  | Dataconstrs : (Constr.t, ('a, 'i) Term.dataconstr) Abwd.t -> any_dataconstrs

type any_codatafields =
  | Codatafields : ('a * 'n * 'et) Term.CodatafieldAbwd.t -> any_codatafields

let register_constructor_names name const constrs =
  List.iter
    (fun (_, constr) ->
      let cname = Constr.to_string constr in
      Scope.define_constr [ cname ] constr const;
      Scope.define_constr (name @ [ cname ]) constr const)
    (List.sort_uniq compare constrs)

let register_field_names name const fields =
  List.iter
    (fun fld ->
      Scope.define_field [ fld ] fld const;
      Scope.define_field (name @ [ fld ]) fld const)
    (List.sort_uniq compare fields)

let register_data_constructors name const =
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
          register_constructor_names name const (go [] constrs)
      | None -> ())
  | _ -> ()

let register_data_fields name const =
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
          register_field_names name const (go [] fields)
      | None -> ())
  | _ -> ()

let parse_term (tm : string) : N.zero check located =
  let p = Parse.Term.parse (`String { content = tm; title = Some "user-supplied term" }) in
  let (Wrap tm) = Parse.Term.final p in
  Postprocess.process Emp tm

let check_type (rty : N.zero check located) : (emp, kinetic) term =
  Reporter.trace "when checking type" @@ fun () ->
  check (Kinetic `Nolet) Ctx.empty rty (universe D.zero)

let check_term (rtm : N.zero check located) (ety : kinetic value) : (emp, kinetic) term =
  Reporter.trace "when checking term" @@ fun () -> check (Kinetic `Nolet) Ctx.empty rtm ety

let assume (name : string) (ty : string) : unit =
  Global.run @@ fun () ->
  let p = Parse.Term.parse (`String { title = Some "constant name"; content = name }) in
  match Parse.Term.final p with
  | Wrap { value = Ident (name, _); _ } ->
      Scope.check_name name None;
      let const = Scope.define name in
      let rty = parse_term ty in
      let cty = check_type rty in
      Global.add const cty (`Axiom, `Nonparametric)
  | _ -> fatal (Invalid_constant_name ([ name ], None))

let def (name : string) (ty : string) (tm : string) : unit =
  Global.run @@ fun () ->
  let p = Parse.Term.parse (`String { title = Some "constant name"; content = name }) in
  match Parse.Term.final p with
  | Wrap { value = Ident (name, _); _ } ->
      Reporter.tracef "when defining %s" (String.concat "." name) @@ fun () ->
      Scope.check_name name None;
      let const = Scope.define name in
      let rty = parse_term ty in
      let rtm = parse_term tm in
      let cty = check_type rty in
      let ety = eval_term (Emp D.zero) cty in
      Reporter.trace "when checking case tree" @@ fun () ->
      Global.add const cty (`Axiom, `Parametric);
      let tree = check (Potential (Constant (const, D.zero), Emp, fun x -> x)) Ctx.empty rtm ety in
      Global.add const cty (`Defined tree, `Parametric);
      register_data_constructors name const;
      register_data_fields name const
  | _ -> fatal (Invalid_constant_name ([ name ], None))

let equal_at (tm1 : string) (tm2 : string) (ty : string) : unit =
  Global.run @@ fun () ->
  let rty = parse_term ty in
  let rtm1 = parse_term tm1 in
  let rtm2 = parse_term tm2 in
  let cty = check_type rty in
  let ety = eval_term (Emp D.zero) cty in
  let ctm1 = check_term rtm1 ety in
  let ctm2 = check_term rtm2 ety in
  let etm1 = eval_term (Emp D.zero) ctm1 in
  let etm2 = eval_term (Emp D.zero) ctm2 in
  match Equal.equal_at Ctx.empty etm1 etm2 ety with
  | Error _ -> raise (Failure "Unequal terms")
  | Ok () -> ()

let unequal_at (tm1 : string) (tm2 : string) (ty : string) : unit =
  Global.run @@ fun () ->
  let rty = parse_term ty in
  let rtm1 = parse_term tm1 in
  let rtm2 = parse_term tm2 in
  let cty = check_type rty in
  let ety = eval_term (Emp D.zero) cty in
  let ctm1 = check_term rtm1 ety in
  let ctm2 = check_term rtm2 ety in
  let etm1 = eval_term (Emp D.zero) ctm1 in
  let etm2 = eval_term (Emp D.zero) ctm2 in
  match Equal.equal_at Ctx.empty etm1 etm2 ety with
  | Error _ -> ()
  | Ok () -> raise (Failure "Equal terms")

let print (tm : string) : unit =
  Global.run @@ fun () ->
  let rtm = parse_term tm in
  match rtm with
  | { value = Synth rtm; loc } ->
      let ctm, ety = synth (Kinetic `Nolet) Ctx.empty { value = rtm; loc } in
      let etm = eval_term (Emp D.zero) ctm in
      Readback.Displaying.run ~env:true @@ fun () ->
      let btm = readback_at Ctx.empty etm ety in
      let utm = unparse Names.empty btm No.Interval.entire No.Interval.entire in
      PPrint.ToChannel.pretty 1.0 (Display.columns ()) stdout (pp_complete_term (Wrap utm) `None);
      print_newline ()
  | _ -> fatal (Nonsynthesizing "argument of print")

let run f =
  Lexer.Specials.run @@ fun () ->
  Parser.Unparse.install ();
  Display.run ~init:Display.default @@ fun () ->
  Annotate.run @@ fun () ->
  Readback.Displaying.run ~env:false @@ fun () ->
  Discrete.run ~env:false @@ fun () ->
  Dim.Endpoints.run ~arity:2 ~refl_char:'e' ~refl_names:[ "refl"; "Id" ] ~internal:true @@ fun () ->
  Reporter.run
    ~emit:(fun d -> Reporter.display d)
    ~fatal:(fun d ->
      Reporter.display d;
      raise (Failure "Fatal error"))
  @@ fun () ->
  Subtype.run @@ fun () ->
  Origin.run @@ fun () ->
  Builtins.install ();
  f ()

let gel_install () =
  def "Gel" "(A B : Set) (R : A → B → Set) → Id Set A B" "A B R ↦ sig a b ↦ ( ungel : R a b )"
