(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013-2014
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

open Mllp_backend

(** {1 CPLEX input format backend} *)

let write_const_cplex_format oc cst =
  output_string oc (if Int.(cst < zero) then "-" else "+");
  output_string oc " ";
  output_string oc (Int.to_string (Int.abs cst))

let write_term_cplex_format oc (term : term) =
  let write_item (c, v) =
    output_string oc " ";
    write_const_cplex_format oc c;
    output_string oc " ";
    output_string oc v.name
  in
  List.iter write_item term

let write_constraint_cplex_format oc (t, c) =
  write_term_cplex_format oc t;
  output_string oc " <= ";
  write_const_cplex_format oc c;
  output_string oc "\n"

let write_bound_cplex_format oc v (min, max) =
  output_string oc "  ";
  output_string oc (Int.to_string min);
  output_string oc " <= ";
  output_string oc v.name;
  output_string oc " <= ";
  output_string oc (Int.to_string max);
  output_string oc "\n"

let write_constraints_cplex_format oc sys =
  if sys.ll_constraints <> []
  then List.iter (write_constraint_cplex_format oc) sys.ll_constraints
  else
    (
      assert (Hashtbl.length sys.ll_vars > 0);
      let name = Hashtbl.fold (fun _ v _ -> v.name) sys.ll_vars "" in
      output_string oc (Printf.sprintf "  + 0 %s >= + 0\n" name)
    )

let write_problem_file oc sys =
  (* Header *)
  output_string oc "Minimize\n";
  write_term_cplex_format oc sys.ll_minimize;
  output_string oc "\n\n";
  (* Constraints *)
  output_string oc "Subject To\n";
  write_constraints_cplex_format oc sys;
  output_string oc "\n";
  (* Bounds *)
  output_string oc "Bounds\n";
  Hashtbl.iter
    (fun _ v -> write_bound_cplex_format oc v sys.ll_bounds)
    sys.ll_vars;
  output_string oc "\n";
  (* Variables *)
  output_string oc "Integers\n";
  Hashtbl.iter
    (fun _ v ->
      output_string oc "  ";
      output_string oc v.name;
      output_string oc "\n")
    sys.ll_vars;
  output_string oc "end\n"

let make_backend_cplex
    output_exts
    make_command
    read_solution_files
    =
  {
    output_exts = output_exts;
    write_problem_file = write_problem_file;
    make_command = make_command;
    read_solution_files = read_solution_files;
  }
