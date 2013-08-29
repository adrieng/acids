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

(** {1 GNU Linear Programming Kit backend} *)

open Mllp_backend

let make_command ~log ~problem ~outputs =
  match outputs with
  | [output; solution] ->
    Printf.sprintf
      "glpsol --cpxlp --log %s -o %s -w %s %s >\\dev\\null"
      log
      output
      solution
      problem
  | _ ->
    assert false

let read_column_names_from_solution_file ic =
  let line = ref "" in

  let skip_until regexp =
    let re = Str.regexp regexp in
    let continue = ref true in
    while !continue do
      try
        line := input_line ic;
        ignore (Str.search_forward re !line 0);
        continue := false
      with
      | Not_found ->
        ()
      | End_of_file ->
        failwith ("XXXX " ^ regexp ^ "XXXX")
    done
  in

  let get num = Str.matched_group num !line in

  let names = ref [] in

  skip_until "Columns: *\\([0-9]+\\)";

  let column_count = int_of_string (get 1) in

  skip_until "Column name";
  skip_until "---";
  for i = 1 to column_count do
      (* i     column_name *)
    skip_until ("^ +" ^ string_of_int i ^ " +\\([^ ]+\\)\\( \\|$\\)");
    names := get 1 :: !names
  done;
  List.rev !names

let read_column_values_from_output_file ordered_names ic sys =
  (* Format:

     m n
     stat obj_val
     r_val[1]
     ...
     r_val[m]
     c_val[1]
     ...
     c_val[n]

     where
     m: row count
     n: column count
     stat: sol status (UNDEF = 1, FEASIBLE = 2, NOFEASIBLE = 4, OPTIMAL = 5)
     obj_val: objective function value
  *)

  (* See GLPK manual, pp. 105-106 *)

  try
    let read_two_integers () =
      let l = input_line ic in
      Scanf.sscanf l "%d %d" (fun i1 i2 -> (Int.of_int i1, Int.of_int i2))
    in

    let read_one_integer () =
      let l = input_line ic in
      Scanf.sscanf l "%d" (fun i -> Int.of_int i)
    in

    let m, n = read_two_integers () in
    let stat, _ = read_two_integers () in

    if stat <> Int.of_int 2 && stat <> Int.of_int 5
    then No_solution
    else
      (
        if n <> Int.of_int (Hashtbl.length sys.ll_vars)
        then Error "bad variable count"
        else
          (
            let rec skip_rows m =
              if Int.(m = zero) then ()
              else (ignore (input_line ic); skip_rows (Int.pred m))
            in
            skip_rows m;

            if Int.of_int (List.length ordered_names) <> n
            then Error "bad output format"
            else
              let read_column_solution solution name =
                let v = Hashtbl.find sys.ll_vars name in
                let i = read_one_integer () in
                Utils.Int_map.add v.id i solution
              in
              Solution
                (List.fold_left
                   read_column_solution
                   Utils.Int_map.empty
                   ordered_names)
          )
      )
  with
  | End_of_file | Scanf.Scan_failure _ ->
    Error "bad output format"

let read_solution_files solutions sys =
  match solutions with
  | [sol_ic; out_ic] ->
    (
      try
        let ordered_names = read_column_names_from_solution_file sol_ic in
        read_column_values_from_output_file ordered_names out_ic sys
      with Failure reason ->
        Error reason
    )
  | _ ->
    assert false

let backend =
  Mllp_backend_cplex.make_backend_cplex
    ["out"; "sol"]
    make_command
    read_solution_files
