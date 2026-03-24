let parse_command str =
  match Parser.Command.parse_single str with
  | _, Some cmd -> cmd
  | _, None -> raise (Failure "expected command")

let parse_fails str =
  Core.Reporter.try_with ~fatal:(fun _ -> true) @@ fun () ->
  ignore (parse_command str);
  false

let () =
  Core.Reporter.run ~fatal:(fun _ -> raise (Failure "fatal error")) ~emit:(fun _ -> ()) @@ fun () ->
  Core.Origin.Origin.run @@ fun () ->
  Parser.Lexer.Specials.run @@ fun () ->
  Parser.Builtins.install ();
  (match parse_command "f x = g x where { g y = y; h : A; h = g x }" with
  | Parser.Command.Command.Clause
      {
        where_block =
          Some
            {
              first = Parser.Command.Local_clause _;
              rest =
                [ (_, Parser.Command.Local_type_sig _); (_, Parser.Command.Local_clause _) ];
              _;
            };
        _;
      } -> ()
  | _ -> raise (Failure "expected clause-local where block"));
  (match parse_command "echo (do { x ← m; y <- n; k x y })" with
  | Parser.Command.Command.Echo _ -> ()
  | _ -> raise (Failure "expected do-notation to parse in echo"));
  assert (parse_fails "f x = y where { postulate A : Set }")
