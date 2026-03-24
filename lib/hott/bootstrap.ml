open Bwd
open Dim
open Core
open Origin
open Value
open Variables
open Reporter

(* Here we bootstrap the HOTT fibrancy data using definitions that are parsed and checked.  The Agdarya code for this is stored in the following three source files, dropped here with ppx_blob. *)

let visible = [%blob "visible.ny"]
let isfibrant = [%blob "isfibrant.ny"]
let fibrancy = [%blob "fibrancy.ny"]

let bootstrap _title content =
  List.iter
    (fun chunk ->
      match Parser.Command.parse_single chunk with
      | _, Some cmd ->
          let _ = Top.Execute.execute_command cmd in
          ()
      | _, None -> ())
    (Top.Execute.split_source_commands_with_boundaries content);
  Top.Execute.flush_pending_commands ()

(* For frobnicating things, we need to look up the defined terms that result from the bootstrapping. *)
let get name =
  match Parser.Scope.lookup name with
  | Some const -> const
  | None -> fatal (Anomaly (String.concat "." name ^ " not in scope"))

let () =
  (* Wrap everything in the standard effect handlers *)
  Top.hott := false;
  Top.run_top ~install_hott:(fun () -> ()) ~interactive:false @@ fun () ->
  (* *)

  (* Load the visible bootstrap file, which defines isBisim and glue. *)
  Check.gel_ok := true;
  bootstrap "visible bootstrap" visible;
  Check.gel_ok := false;
  let glue = get [ "glue" ] in

  (* Mark glue as being glue. *)
  (match Global.find glue with
  | _, (`Defined (Lam (_, a, Lam (_, b, Lam (_, r, Lam (_, re, Canonical (Codata c)))))), param)
    -> (
      match
        ( D.compare_zero (dim_variables a),
          D.compare_zero (dim_variables b),
          D.compare_zero (dim_variables r),
          D.compare_zero (dim_variables re),
          D.compare c.dim Hott.dim,
          c.eta )
      with
      | Zero, Zero, Zero, Zero, Eq, Eta ->
          let glue_def : Global.definition =
            ( `Defined
                (Term.Lam
                   ( `Explicit,
                     a,
                     Term.Lam
                       ( `Explicit,
                         b,
                         Term.Lam
                           ( `Explicit,
                             r,
                             Term.Lam
                               ( `Explicit,
                                 re,
                                 Term.Canonical (Term.Codata { c with is_glue = Some Glue }) ) ) ) )),
              param ) in
          Global.set glue glue_def
      | _ -> fatal (Anomaly "glue has wrong dimension"))
  | _ -> fatal (Anomaly "glue undefined"));

  (* Load the hidden isfibrant bootstrap file *)
  let isfibrant_file = File.make (`Other "isfibrant bootstrap") in
  ( Origin.with_file ~holes_allowed:false isfibrant_file @@ fun () ->
    bootstrap "isfibrant bootstrap" isfibrant;

    (* Use this to compute the types of fibrancy fields. *)
    let isfibrant = get [ "isFibrant" ] in
    match Global.find isfibrant with
    | _, (`Defined (Lam (_, x, Canonical (Codata { eta = Noeta; dim; fields; _ }))), _) -> (
        match (D.compare_zero (dim_variables x), D.compare_zero dim) with
        | Zero, Zero ->
            Fibrancy.fields :=
              (* The recursive "id" field is not exposed to the user; they access it simply by instantiating higher-dimensional types. *)
              Some
                (Bwd.filter
                   (fun (Term.CodatafieldAbwd.Entry (f, _)) ->
                     match Field.equal f Fibrancy.fid with
                     | Eq -> false
                     | Neq -> true)
                   fields)
        | _ -> fatal (Anomaly "isFibrant has wrong dimension"))
    | _ -> fatal (Anomaly "isFibrant has wrong shape") );

  (* Load the hidden bootstrap file.  This requires that types already *have* fibrancy fields, so it has to be a separate file from hott-isfibrant. *)
  let fibrancy_file = File.make (`Other "fibrancy bootstrap") in
  ( Origin.with_file ~holes_allowed:false fibrancy_file @@ fun () ->
    bootstrap "fibrancy bootstrap" fibrancy;

    let eq_trr = get [ "eq"; "trr" ] in
    let eq_trr2 = get [ "eq"; "trr2" ] in
    let id_rtr = get [ "Id_rtr" ] in
    let fib_rtr = get [ "fib_rtr" ] in
    let id_pi_rtr = get [ "id_pi_rtr" ] in
    let glue_rtr = get [ "glue_rtr" ] in
    let fib_pi = get [ "fib_pi" ] in
    let fib_glue = get [ "fib_glue" ] in

    (* We remove the eq.trr's from the definition of fib_rtr, and the eq.trr2's from id_rtr, since they are always unnecessary computationally.  This doesn't seem to materially affect performance, but it's cleaner. *)
    (match Global.find fib_rtr with
    | _, (`Defined (Lam (_, aa, Lam (_, bb, Lam (_, e, Struct ({ fields; eta = Noeta; _ } as s))))), param) ->
        let fields =
          Bwd.map
            (function
              | Term.StructfieldAbwd.Entry (f, Higher tms) ->
                  let tms =
                    Term.PlusPbijmap.mmap
                      {
                        map =
                          (fun _ [ x ] ->
                            Option.map
                              (function
                                | Term.PlusFam.PlusFam
                                    ( p,
                                      Term.Lam
                                        ( _,
                                          b,
                                          Term.Realize
                                            (Term.App
                                               ( _,
                                                 Term.App
                                                   ( _,
                                                     Term.App
                                                       ( _,
                                                         Term.App
                                                           ( _,
                                                             Term.App
                                                               ( _,
                                                                 Term.App (_, Const c, _),
                                                                 _ ),
                                                             _ ),
                                                         _ ),
                                                     _ ),
                                                 tm )) ) )
                                  when c = eq_trr ->
                                    Term.PlusFam.PlusFam
                                      (p, Term.Lam (`Explicit, b, Term.Realize (CubeOf.find_top tm)))
                                | y -> y)
                              x);
                      }
                      [ tms ] in
                  Term.StructfieldAbwd.Entry (f, Higher tms)
              | s -> s)
            fields in
        Global.set fib_rtr
          (`Defined
             (Term.Lam
                (`Explicit, aa, Term.Lam (`Explicit, bb, Term.Lam (`Explicit, e, Term.Struct { s with fields })))),
           param)
    | _ -> ());
    (match Global.find id_rtr with
    | _,
      (`Defined
        (Lam
           ( _,
             a0,
             Lam
               ( _,
                 a1,
                 Lam
                   ( _,
                     a2,
                     Lam
                       ( _,
                         b0,
                         Lam
                           ( _,
                             b1,
                             Lam
                               ( _,
                                 b2,
                                 Lam
                                   ( _,
                                     e0,
                                     Lam
                                       ( _,
                                         e1,
                                         Lam
                                           ( _,
                                             e2,
                                             Lam (_, x0, Lam (_, x1, Struct s)) ) ) ) ) ) ) ) ) )),
       param) ->
        let fields =
          Bwd.map
            (function
              | Term.StructfieldAbwd.Entry
                  ( fld,
                    Lower
                      ( Lam
                          ( _,
                            b,
                            Term.Realize
                              (Term.App
                                 ( _,
                                   Term.App
                                     ( _,
                                       Term.App
                                         ( _,
                                           Term.App
                                             ( _,
                                               Term.App
                                                 ( _,
                                                   Term.App
                                                     ( _,
                                                       Term.App
                                                         ( _,
                                                           Term.App (_, Const c, _),
                                                           _ ),
                                                         _ ),
                                                     _ ),
                                                 _ ),
                                             _ ),
                                         _ ),
                                   tm )) ),
                        l ) )
                when c = eq_trr2 ->
                  Term.StructfieldAbwd.Entry
                    (fld, Lower (Term.Lam (`Explicit, b, Term.Realize (CubeOf.find_top tm)), l))
              | y -> y)
            s.fields in
        let tm =
          let body = Term.Struct { s with fields } in
          let body = Term.Lam (`Explicit, x1, body) in
          let body = Term.Lam (`Explicit, x0, body) in
          let body = Term.Lam (`Explicit, e2, body) in
          let body = Term.Lam (`Explicit, e1, body) in
          let body = Term.Lam (`Explicit, e0, body) in
          let body = Term.Lam (`Explicit, b2, body) in
          let body = Term.Lam (`Explicit, b1, body) in
          let body = Term.Lam (`Explicit, b0, body) in
          let body = Term.Lam (`Explicit, a2, body) in
          let body = Term.Lam (`Explicit, a1, body) in
          Term.Lam (`Explicit, a0, body) in
        Global.set id_rtr (`Defined tm, param)
    | _ -> ());

    (* We adjust the case tree boundary for id_pi_rtr to avoid exposing that constant to the user when a higher fibrancy field is applied only to a function but not a further argument. *)
    (match Global.find id_pi_rtr with
    | _,
      (`Defined
        (Lam
           ( _,
             a0,
             Lam
               ( _,
                 a1,
                 Lam
                   ( _,
                     a2,
                     Lam
                       ( _,
                         b0,
                         Lam
                           ( _,
                             b1,
                             Lam (_, b2, Lam (_, f0, Lam (_, f1, Struct s))) ) ) ) ) )),
       param) ->
        let fields =
          Bwd.map
            Term.StructfieldAbwd.(
              function
              | Entry (fld, Lower (Lam (_, f, Lam (_, a, Realize tm)), l)) ->
                  Entry
                    ( fld,
                      Lower
                        (Term.Lam (`Explicit, f, Term.Realize (Term.Lam (`Explicit, a, tm))), l)
                    )
              | Entry
                  (fld, Lower (Lam (_, f, Lam (_, a0, Lam (_, a1, Lam (_, a2, Realize tm)))), l))
                ->
                  Entry
                    ( fld,
                      Lower
                        ( Term.Lam
                            ( `Explicit,
                              f,
                              Term.Realize
                                (Term.Lam
                                   ( `Explicit,
                                     a0,
                                     Term.Lam (`Explicit, a1, Term.Lam (`Explicit, a2, tm)) )) ),
                          l ) )
              | s -> s)
            s.fields in
        let tm =
          let body = Term.Struct { s with fields } in
          let body = Term.Lam (`Explicit, f1, body) in
          let body = Term.Lam (`Explicit, f0, body) in
          let body = Term.Lam (`Explicit, b2, body) in
          let body = Term.Lam (`Explicit, b1, body) in
          let body = Term.Lam (`Explicit, b0, body) in
          let body = Term.Lam (`Explicit, a2, body) in
          let body = Term.Lam (`Explicit, a1, body) in
          Term.Lam (`Explicit, a0, body) in
        Global.set id_pi_rtr (`Defined tm, param)
    | _ -> fatal (Anomaly "id_pi_rtr undefined"));

    (* As with id_pi_rtr, so with glue_rtr *)
    (match Global.find glue_rtr with
    | _, (`Defined (Lam (_, aa, Lam (_, bb, Lam (_, rr, Lam (_, re, Lam (_, a, Lam (_, b, Struct s))))))), param) ->
        let fields =
          Bwd.map
            Term.StructfieldAbwd.(
              function
              | Entry
                  ( fld,
                    Lower
                      (Term.Lam
                         (`Explicit, r, Term.Struct { dim; fields; eta = Eta; energy = Potential }), l)
                  )
                ->
                  let fields =
                    Bwd.map
                      Term.StructfieldAbwd.(
                        function
                        | Entry (stfld, Lower (Realize y, stl)) -> Entry (stfld, Lower (y, stl))
                        | _ -> fatal (Anomaly "glue_rtr has wrong shape"))
                      fields in
                  Entry
                    ( fld,
                      Lower
                        (Term.Lam
                           ( `Explicit,
                             r,
                             Term.Realize
                               (Term.Struct { dim; fields; eta = Eta; energy = Kinetic } ) ),
                         l )
                    )
              | x -> x)
            s.fields in
        let tm =
          let body = Term.Struct { s with fields } in
          let body = Term.Lam (`Explicit, b, body) in
          let body = Term.Lam (`Explicit, a, body) in
          let body = Term.Lam (`Explicit, re, body) in
          let body = Term.Lam (`Explicit, rr, body) in
          let body = Term.Lam (`Explicit, bb, body) in
          Term.Lam (`Explicit, aa, body) in
        Global.set glue_rtr (`Defined tm, param)
    | _ -> fatal (Anomaly "glue_rtr_rtr undefined"));

    (* Now we pull out the fields from the definition of fib_pi to insert them in Fibrancy.pi. *)
    (match Global.find fib_pi with
    | _, (`Defined (Lam (_, a, Lam (_, b, Struct { dim; fields; eta = Noeta; energy = Potential }))), _)
      -> (
        match
          (D.compare_zero (dim_variables a), D.compare_zero (dim_variables b), D.compare_zero dim)
        with
        | Zero, Zero, Zero ->
            (* We rearrange the end of the case trees for tr and lift so that after applying to a single function argument they compute to an abstraction.  This is actually not what we'd want in principle, but we do it for consistency with the higher-dimensional case where we don't seem to have another option. *)
            let fields =
              Bwd.map
                (function
                  | Term.StructfieldAbwd.Entry (f, Higher tms) ->
                      let tms =
                        Term.PlusPbijmap.mmap
                          {
                            map =
                              (fun _ [ x ] ->
                                Option.map
                                  (function
                                    | Term.PlusFam.PlusFam (p, Lam (_, f, Lam (_, a, Realize tm))) ->
                                        Term.PlusFam.PlusFam
                                          ( p,
                                            Term.Lam
                                              (`Explicit, f, Term.Realize (Term.Lam (`Explicit, a, tm))) )
                                    | y -> y)
                                  x);
                          }
                          [ tms ] in
                      Term.StructfieldAbwd.Entry (f, Higher tms)
                  | s -> s)
                fields in
            Fibrancy.pi := Some fields
        | _ -> fatal (Anomaly "fib_pi has wrong dimension"))
    | _ -> fatal (Anomaly "fib_pi has wrong shape"));

    (* And similarly for Fibrancy.glue. *)
    (match Global.find fib_glue with
    | _, (`Defined tm, _) -> (
        match tm with
        | Lam
            ( _,
              a,
              Lam
                ( _,
                  b,
                  Lam
                    ( _,
                      r,
                      Lam (_, re, Struct { dim; fields; eta = Noeta; energy = Potential }) ) ) )
          -> (
            match
              ( D.compare_zero (dim_variables a),
                D.compare_zero (dim_variables b),
                D.compare_zero (dim_variables r),
                D.compare_zero (dim_variables re),
                D.compare dim Hott.dim )
            with
            | Zero, Zero, Zero, Zero, Eq -> Fibrancy.glue := Some fields
            | _ -> fatal (Anomaly "fib_glue has wrong dimension"))
        | _ -> fatal (Anomaly "fib_glue has wrong shape"))
    | _ -> fatal (Anomaly "fib_glue has wrong shape") ) );

  let ofile =
    if Array.length Sys.argv <> 2 then (
      print_endline "usage: bootstrap outfile";
      exit 1)
    else Sys.argv.(1) in
  Out_channel.with_open_bin ofile @@ fun chan -> Io.marshal chan isfibrant_file fibrancy_file
