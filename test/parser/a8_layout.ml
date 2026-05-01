let parse_command str =
  match Parser.Command.parse_single str with
  | _, Some cmd -> cmd
  | _, None -> raise (Failure "expected command")

let parse_term str =
  Parser.Parse.Term.final (Parser.Parse.Term.parse (`String { content = str; title = Some "term" }))

let parse_fails str =
  Core.Reporter.try_with ~fatal:(fun _ -> true) @@ fun () ->
  ignore (parse_command str);
  false

let () =
  Testutil.Repl.run @@ fun () ->
  (match parse_command "data Jd (X : Set) (x : X) : X → Set where\n  rfl : Jd X x x" with
  | Parser.Command.Command.Data_decl _ -> ()
  | _ -> raise (Failure "expected layout data declaration"));
  (match parse_command "record Pair (A B : Set) : Set where\n  field\n    fst : A\n    snd : B" with
  | Parser.Command.Command.Record_decl _ -> ()
  | _ -> raise (Failure "expected layout record declaration"));
  (match parse_command "module M where\n  postulate\n    A : Set" with
  | Parser.Command.Command.Module_decl _ -> ()
  | _ -> raise (Failure "expected layout module declaration"));
  (match parse_command "f x = y where\n  g z = z" with
  | Parser.Command.Command.Clause { body = Parser.Command.Body { where_block = Some _; _ }; _ } -> ()
  | _ -> raise (Failure "expected layout clause-local where block"));
  ignore (parse_term "let\n  x : A\n  x = x\nin x");
  ignore (parse_term "let { x : A; x = x } in x");
  ignore (parse_term "case x of\n  zero → zero\n  suc y → y");
  ignore (parse_term "case x of { zero → zero; suc y → y }");
  ignore (parse_term "do\n  y ← m\n  y");
  ignore (parse_term "do { y ← m; y }");
  (match parse_command "data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }" with
  | Parser.Command.Command.Data_decl _ -> ()
  | _ -> raise (Failure "expected explicit-brace data declaration"));
  assert (parse_fails "data Empty : Set where");
  assert (parse_fails "module Bad where");
  ()
