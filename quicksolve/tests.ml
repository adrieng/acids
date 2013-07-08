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

let eq ?(eq = (=)) print act exp =
  let b = eq exp act in
  if not b
  then
    Format.printf "{unexpected %a,@ expected %a} "
      print act
      print exp;
  b

let eq_int = eq Int.print

let eq_word =
  let print_word fmt w = Format.fprintf fmt "[%a]" Pword.print_word w in
  eq print_word

(* Testing Pword *)

let i = Int.of_int

let p s =
  let lexbuf = Lexing.from_string s in
  let w = Parser.pword_start Lexer.token lexbuf in
  Resolution_utils.pword_of_tree w

let w s =
  let lexbuf = Lexing.from_string s in
  let w = Parser.word_start Lexer.token lexbuf in
  Resolution_utils.word_of_tree w

let iof =
  let w1 = p "1^4 (1)" in
  let w2 = p "0^3 1 (2 0 3^2 0)" in
  let w3 = p "0 2^3 4 (1)" in
  [
    (fun () -> eq_int (Pword.iof w1 (i 1)) (i 1));
    (fun () -> eq_int (Pword.iof w1 (i 2)) (i 2));
    (fun () -> eq_int (Pword.iof w1 (i 3)) (i 3));
    (fun () -> eq_int (Pword.iof w1 (i 4)) (i 4));
    (fun () -> eq_int (Pword.iof w1 (i 7)) (i 7));
    (fun () -> eq_int (Pword.iof w1 (i 9)) (i 9));

    (fun () -> eq_int (Pword.iof w2 (i 3)) (i 5));
    (fun () -> eq_int (Pword.iof w2 (i 5)) (i 7));
    (fun () -> eq_int (Pword.iof w2 (i 15)) (i 13));

    (fun () -> eq_int (Pword.iof w3 (i 3)) (i 3));
  ]

let alap =
  let l =
    [
      w "0^3 1", i 1, i 4, i 1, [(i 1, i 4)];
      w "1 0^3", i 1, i 4, i 1, [(i 1, i 1)];
    ]
  in
  let make (w, max_burst, size, nbones, iof) () =
    eq_word
      (Pword.make_word_alap ~max_burst ~size ~nbones iof)
      w
  in
  List.map make l

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
  @ name_tests "make_word_alap" alap

let run_test (failed, passed, total) (test_name, test) =
  Format.printf "%s: @[" test_name;
  let nfailed, npassed =
    (* if (try test () with _ -> Format.printf "{exception} "; false) *)
    if test ()
    then failed, passed + 1
    else failed + 1, passed
  in
  Format.printf "%s@]@."
    (if nfailed > failed then "KO" else "OK")
  ;
  flush stdout;
  nfailed, npassed, total + 1

let init = 0, 0, 0

let self_test () =
  let failed, passed, total = List.fold_left run_test init tests in
  Format.printf "%d tests, %d passed, %d failed@."
    total
    passed
    failed;
  flush stdout
