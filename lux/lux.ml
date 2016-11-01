open Types

let box v ty = Box (Pword.(make empty (singleton (Int.of_int v))), ty)

let t1 =
  Fun
    (
      box 2 (Prod (Unit, Fun (Stream Float, Stream Char))),
      Fun
        (
          Stream Int,
          Prod
            (
              Unit,
              box 2 (box 3 (Stream Bool))
            )
        )
    );;

let _ =
  let args =
    [
      "-utf8",
      Arg.Symbol (["yes"; "no"], Options.yes_no Options.pp_unicode),
      " use UTF-8 pretty-printing (default: yes)";
    ]
  in
  let unknown s =
    Printf.printf "I don't know what to do with %s\n" s
  in
  Arg.parse args unknown "Lux v0.0";
  Format.printf "Initial: @[%a@]@\n" print_ty t1;
  Format.printf "Normalized: @[%a@]@\n" print_ty (normalize t1);
  Format.printf "@?"
