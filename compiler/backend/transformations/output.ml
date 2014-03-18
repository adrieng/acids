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

(* {2 Errors} *)

type error =
  | Unknown_target of string

exception Output_error of error

let print_error fmt err =
  match err with
  | Unknown_target name ->
    Format.fprintf fmt "Unknown target %s" name

let unknown_target name =
  raise (Output_error (Unknown_target name))

(* {2 Table} *)

let targets =
  [
    "c", Target_c.pass;
  ]

let select_pass _ =
  let target_name = !Compiler_options.target in
  try List.assoc target_name targets
  with Not_found -> unknown_target target_name

let output_code ctx (code : Target.target_code) =
  ctx, code#serialize ()

let pass =
  let open Pass_manager in
  P_sel select_pass +>+ P_transform (make_transform "output" output_code)

let _ =
  Compiler_options.target_list := List.map fst targets;
  Compiler_options.target := fst (List.hd targets)
