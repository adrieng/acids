(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013
 *
 * This file is part of Acid Synchrone.
 *
 * nsched is free software: you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any later
 * version.
 *
 * nsched is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * nsched. If not, see <http://www.gnu.org/licenses/>.
 *)

(* Testing Pword *)

let p s =
  let lexbuf = Lexing.from_string s in
  let w = Parser.word Lexer.token lexbuf in
  Resolution_utils.pword_of_tree w

let iof =
  let open Int in
  let w = p "1^4 (1)" in
  [
    (fun () -> Pword.iof w (of_int 1) = of_int 1);
    (fun () -> Pword.iof w (of_int 2) = of_int 2);
    (fun () -> Pword.iof w (of_int 3) = of_int 3);
    (fun () -> Pword.iof w (of_int 4) = of_int 4);
    (fun () -> Pword.iof w (of_int 7) = of_int 7);
    (fun () -> Pword.iof w (of_int 9) = of_int 9);
  ]

(* Stupid unit test framework *)

let name_tests base_name tests =
  let _, tests =
    List.fold_left
      (fun (i, tests) test ->
        i + 1, (base_name ^ "_" ^ string_of_int i, test) :: tests)
      (0, [])
      tests
  in
  List.rev tests

let tests =
  name_tests "iof" iof

let run_test (failed, passed, total) (test_name, test) =
  let nfailed, npassed =
    if (try test () with _ -> false)
    then failed, passed + 1
    else failed + 1, passed
  in
  Printf.printf "%s: %s\n"
    test_name
    (if nfailed > failed then "KO" else "OK")
  ;
  flush stdout;
  nfailed, npassed, total + 1

let init = 0, 0, 0

let self_test () =
  let failed, passed, total = List.fold_left run_test init tests in
  Printf.printf "%d tests, %d passed, %d failed\n"
    total
    passed
    failed
