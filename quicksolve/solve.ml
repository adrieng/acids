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

let verbose = ref 0

let global_max_burst = ref 1

let global_max_int = ref Pervasives.max_int

let k = ref 0

let k' = ref 1

let unrefined = ref false

let complete = ref false

let profile = ref false

let ilp_solvers =
  [
    "glpk";
    "gurobi";
  ]

let ilp_solver = ref (List.hd ilp_solvers)

let parse_file filen =
  Solver_utils.set_current_file_name filen;
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
  let sys =
    let open Resolution in
    let open Resolution_options in
    let opts =
      [
        "verbose", Int (Int.of_int !verbose);
        "check", Bool (!verbose >= 1);
        "max_burst", Int (Int.of_int !global_max_burst);
        "max_int", Int (Int.of_int !global_max_int);
        "k", Int (Int.of_int !k);
        "k'", Int (Int.of_int !k');
        "unrefined", Bool !unrefined;
        "complete", Bool !complete;
        "profile", Bool !profile;
        "ilp", String !ilp_solver;
      ]
    in

    let add options (k, v) =
      let already_present =
        try ignore (find options k); true with Not_found -> false
      in
      if already_present then options else add options (make k v)
    in

    { sys with options = List.fold_left add sys.options opts; }
  in

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
  | Could_not_solve err ->
    Format.printf "%a@." Resolution_errors.print_error err;
    exit_code := 1
  | Resolution_options.Option_error (opt, exp_ty, act_ty) ->
    Format.printf "option %s is of type %s but was expected to be of type %s@."
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
        "-test",
        Unit Tests.self_test,
        " run self tests";

        "-v",
        Int (fun i -> assert (i >= 0); verbose := i),
        " verbosity";

        "-mb",
        Int (fun i -> assert (i >= 0); global_max_burst := i),
        " maximum burst";

        "-mi",
        Int (fun i -> assert (i >= 0); global_max_int := i),
        " maximum int";

        "-nbones_pref",
        Int (fun i -> assert (i >= 0); k := i),
        " prefix adjustment factor (concrete resolution)";

        "-nbones",
        Int (fun i -> assert (i >= 1); k' := i),
        " period adjustment factor (concrete resolution)";

        "-unrefined",
        Unit (fun () -> unrefined := true),
        " build unrefined precedence constraints (concrete resolution)";

        "-complete",
        Unit (fun () -> complete := true),
        " disable incomplete heuristics (concrete resolution)";

        "-profile",
        Unit (fun () -> profile := true),
        " enable profiling messages";

        "-ilp",
        Symbol (ilp_solvers, (fun s -> ilp_solver := s)),
        " choose ilp solver (default: " ^ !ilp_solver ^ ")";
      ]
  in
  let files = ref [] in
  let add f = files := f :: !files in
  Arg.parse opts
    add
    (Printf.sprintf "Usage: %s [opts] problem_file\n" Sys.argv.(0));
  List.iter do_file !files;
  flush stdout;
  exit !exit_code
