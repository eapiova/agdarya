let parse_command str =
  match Parser.Command.parse_single str with
  | _, Some cmd -> cmd
  | _, None -> raise (Failure "expected command")

let () =
  Core.Reporter.run ~fatal:(fun _ -> raise (Failure "fatal error")) ~emit:(fun _ -> ()) @@ fun () ->
  Core.Origin.Origin.run @@ fun () ->
  Parser.Lexer.Specials.run @@ fun () ->
  Parser.Builtins.install ();
  ignore (parse_command "SqrtA : Set");
  ignore (parse_command "SqrtA = codata [ root⟨e⟩ x : A ]");
  ignore (parse_command "sqrt_a : SqrtA");
  ignore (parse_command "sqrt_a = [ root⟨e⟩ ↦ a ]");
  ignore (parse_command "echo (s root⟨1⟩)");
  let old_named_higher_field_rejected =
    Core.Reporter.try_with ~fatal:(fun _ -> true) @@ fun () ->
    let _ = parse_command "echo (s .root.1)" in
    false in
  assert old_named_higher_field_rejected
