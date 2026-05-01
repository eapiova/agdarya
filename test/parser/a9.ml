let parse_command str =
  match Parser.Command.parse_single str with
  | _, Some cmd -> cmd
  | _, None -> raise (Failure "expected command")

let parse_fails str =
  Core.Reporter.try_with ~fatal:(fun _ -> true) @@ fun () ->
  ignore (parse_command str);
  false

let () =
  Testutil.Repl.run @@ fun () ->
  (match parse_command "pred n with n\n... | zero = zero\n... | suc m = m" with
  | Parser.Command.Command.Clause
      {
        body =
          Parser.Command.With_block
            { items = [ _ ]; branches = [ { patterns = [ _ ]; _ }; { patterns = [ _ ]; _ } ] };
        _;
      } -> ()
  | _ -> raise (Failure "expected with-clause to parse"));
  (match parse_command "sameNat m n with m | n\n... | zero | zero = zero\n... | suc k | suc l = zero" with
  | Parser.Command.Command.Clause
      {
        body =
          Parser.Command.With_block
            { items = [ _; _ ]; branches = [ { patterns = [ _; _ ]; _ }; { patterns = [ _; _ ]; _ } ] };
        _;
      } -> ()
  | _ -> raise (Failure "expected multi-with-clause to parse"));
  (match parse_command
           "predPred n with n\n... | zero = zero\n... | suc m with m\n... | zero = zero\n... | suc k = k"
   with
  | Parser.Command.Command.Clause
      {
        body =
          Parser.Command.With_block
            {
              branches =
                [
                  { rhs = Parser.Command.Body _; _ };
                  { rhs = Parser.Command.With_block { items = [ _ ]; branches = [ _; _ ] }; _ };
                ];
              _;
            };
        _;
      } -> ()
  | _ -> raise (Failure "expected nested with-clause to parse"));
  (match parse_command "f x rewrite p = x" with
  | Parser.Command.Command.Clause
      { body = Parser.Command.Rewrite_block { proofs = [ _ ]; tail = Parser.Command.Body _ }; _ } ->
      ()
  | _ -> raise (Failure "expected rewrite-clause to parse"));
  (match parse_command "f x rewrite p | q = x" with
  | Parser.Command.Command.Clause
      { body = Parser.Command.Rewrite_block { proofs = [ _; _ ]; tail = Parser.Command.Body _ }; _ } ->
      ()
  | _ -> raise (Failure "expected multi-rewrite-clause to parse"));
  (match parse_command "plusZeroR (suc n) rewrite plusZeroR n = refl (suc n)" with
  | Parser.Command.Command.Clause
      { body = Parser.Command.Rewrite_block { proofs = [ _ ]; tail = Parser.Command.Body _ }; _ } ->
      ()
  | _ -> raise (Failure "expected recursive rewrite-clause to parse"));
  assert (parse_fails "... | zero = zero");
  assert (parse_fails "f x with y");
  assert (parse_fails "f x rewrite p")
