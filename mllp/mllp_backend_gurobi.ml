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

open Mllp_backend

let make_command ~log ~problem ~outputs =
  match outputs with
  | [solution] ->
    Printf.sprintf
      "gurobi_cl LogFile=%s ResultFile=%s %s > /dev/null"
      log
      solution
      problem
  | _ ->
    assert false

let read_solution_file ic sys =
  let line = ref "" in

  let read_line () = line := input_line ic in

  let matches re =
    let re = Str.regexp re in
    try ignore (Str.search_forward re !line 0); true with Not_found -> false
  in

  let get i = Str.matched_group i !line in

  (* Read one line *)
  let could_read_header =
    try
      read_line ();
      matches "^# Objective value = \\([0-9]+\\)"
    with End_of_file ->
      false
  in

  if could_read_header
  then
    let rec read_values sol count =
      if count = 0
      then Solution sol
      else
        (
          read_line ();
          if not (matches "^\\([a-zA-Z0-9'_]+\\) +\\([0-9]\\)+")
          then Error ("bad format (unexpected " ^ !line ^ ")")
          else
            let name = get 1 in
            let value = Int.of_int (Utils.int_of_string_exp !line) in
            let v = Hashtbl.find sys.ll_vars name in
            read_values (Utils.Int_map.add v.id value sol) (count - 1)
        )
    in
    read_values Utils.Int_map.empty (Hashtbl.length sys.ll_vars)
  else
    No_solution

let read_solution_files ic_l sys =
  match ic_l with
  | [ic] ->
    read_solution_file ic sys
  | _ ->
    assert false

let backend =
  Mllp_backend_cplex.make_backend_cplex
    ["sol"]
    make_command
    read_solution_files
