open Dim
open Reporter
open Value
open Equal
open Norm
open Readback

type unify_error =
  | Rigid_mismatch of Unequal.t
  | Flex_stuck
  | Occurs_check

type kinetic_evar = KE : ('a, 'b, kinetic) Meta.t -> kinetic_evar

let same_meta : type a1 b1 s1 a2 b2 s2. (a1, b1, s1) Meta.t -> (a2, b2, s2) Meta.t -> bool =
 fun m1 m2 ->
  match Meta.compare m1 m2 with
  | Eq -> true
  | Neq -> false

let unsolved_evar_head : kinetic value -> kinetic_evar option = function
  | Neu { head = Meta { meta; ins; _ }; args = Emp; _ }
    when Meta.is_evar meta && Option.is_some (is_id_ins ins) -> (
      match Global.find_meta meta with
      | { tm = `Undefined; energy = Kinetic; _ } -> Some (KE meta)
      | _ -> None)
  | _ -> None

let solve : type a b c d.
    (c, d) Ctx.t -> (a, b, kinetic) Meta.t -> kinetic value -> (unit, unify_error) result =
 fun _ctx meta rhs ->
  let meta_ctx = eval_ctx (Global.find_meta meta).termctx in
  Global.set_meta meta ~tm:(readback_val meta_ctx rhs);
  Ok ()

 let unify : type a b.
    (a, b) Ctx.t -> kinetic value -> kinetic value -> kinetic value -> (unit, unify_error) result =
 fun ctx lhs rhs _ty ->
  match (unsolved_evar_head lhs, unsolved_evar_head rhs) with
  | Some (KE meta), Some (KE meta') when same_meta meta meta' -> Ok ()
  | Some (KE meta), _ -> solve ctx meta rhs
  | _, Some (KE meta) -> solve ctx meta lhs
  | _ -> (
      match equal_val ctx lhs rhs with
      | Ok () -> Ok ()
      | Error why -> Error (Rigid_mismatch why))
