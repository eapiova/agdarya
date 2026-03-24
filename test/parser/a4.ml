let parse_command str =
  match Parser.Command.parse_single str with
  | _, Some cmd -> cmd
  | _, None -> raise (Failure "expected command")

let () =
  Core.Reporter.run ~fatal:(fun _ -> raise (Failure "fatal error")) ~emit:(fun _ -> ()) @@ fun () ->
  Core.Origin.Origin.run @@ fun () ->
  Parser.Lexer.Specials.run @@ fun () ->
  Parser.Builtins.install ();
  (match parse_command "data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }" with
  | Parser.Command.Command.Data_decl _ -> ()
  | _ -> raise (Failure "expected data declaration"));
  (match parse_command "record Pair (A B : Set) : Set where { field fst : A; snd : B }" with
  | Parser.Command.Command.Record_decl _ -> ()
  | _ -> raise (Failure "expected record declaration"));
  ignore (parse_command "plus1 n = case n of λ { zero → suc zero ; suc m → suc (suc m) }");
  let constructor_clause_rejected =
    Core.Reporter.try_with ~fatal:(fun d ->
        match d.message with
        | Core.Reporter.Code.Unsupported_record_constructor_clause -> true
        | _ -> false)
    @@ fun () ->
    let _ = parse_command "record Bad : Set where { constructor _,_ }" in
    false
  in
  assert constructor_clause_rejected
