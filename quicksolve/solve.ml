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

open Resolution
open Resolution_errors

let parse_file filen =
  try
    let ic =
      try open_in filen
      with Sys_error _ ->
        Printf.eprintf "Could not open file %s\n" filen;
        exit 1
    in
    let lexbuf = Lexing.from_channel ic in
    let sys_l = Parser.file Lexer.token lexbuf in
    close_in ic;
    sys_l
  with
  | Lexer.Lexical_error loc ->
    Format.eprintf "%aLexical error: %s@."
      Loc.print loc.Loc.l_loc
      loc.Loc.l_contents;
    exit 1
  | Solver_utils.Parse_error loc ->
    Format.printf "%aSyntax error@." Loc.print loc;
    exit 1

let exit_code = ref 0

let do_sys sys =
  Format.printf "System: @[%a@]@\n" print_system sys;
  try
    let print_aff fmt (k, w) =
      Format.fprintf fmt "%s = %a"
        k
        (Tree_word.print_upword_int Int.print) w
    in
    let sol = Solution.fold (fun k w acc -> (k, w) :: acc) (solve sys) [] in
    Format.printf "Solution: @[{@ %a@ }@]@."
      (Utils.print_list_r print_aff ",") sol;
  with
  | Could_not_solve Constant_inconsistency ->
    Format.printf "Inconsistent constants@.";
    exit_code := 1
  | Could_not_solve Rate_inconsistency ->
    Format.printf "Inconsistent rates@.";
    exit_code := 1
  | Could_not_solve Precedence_inconsistency ->
    Format.printf "Inconsistent precedences@.";
    exit_code := 1
  | Could_not_solve (Internal_error sol) ->
    Format.printf "The solver returned an incorrect solution@\n@[{@ %a@ }@]@."
      (Utils.Env.print
         Utils.print_string
         (Tree_word.print_upword_int Int.print)) sol;
    exit_code := 1
  | Resolution_options.Option_error (opt, exp_ty, act_ty) ->
    Format.printf "Option %s is of type %s but was expected to be of type %s@."
      opt
      act_ty
      exp_ty;
    exit_code := 1

let do_file filen =
  let sys_l = parse_file filen in
  Format.printf "Read %d systems from %s@\n" (List.length sys_l) filen;
  List.iter do_sys sys_l

let _ =
  let opts =
    let open Arg in
    align
      [
        "-test", Unit Tests.self_test, " run self tests";
      ]
  in
  let files = ref [] in
  let add f = files := f :: !files in
  Arg.parse opts add (Printf.sprintf "Usage: %s [opts] problem_file\n" Sys.argv.(0));
  List.iter do_file !files;
  flush stdout;
  exit !exit_code
