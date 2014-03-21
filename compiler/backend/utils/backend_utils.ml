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

open Obc

let map_to_machines f_mach ctx file =
  ctx,
  {
    f_name = file.f_name;
    f_type_defs = file.f_type_defs;
    f_machines = List.map f_mach file.f_machines;
  }

let make_transform name tr =
  let open Pass_manager in
  P_transform
    (make_transform
       ~ext:"obc"
       ~print_out:Obc_printer.print_file
       name
       tr)

(******************************************************************************)
(* {2 Runtime stuff} *)

(* Runtime module name *)
let runtime_name = "Rt"

(* Built-in machines *)
let builtin_name = "builtin"
let pword_name = "pword"
let buffer_name = "buffer"
let boxed_name = "boxed"

(* Method names *)
let create_name = "create"
let destroy_name = "destroy"
let reset_name = "reset"
let step_name = "step"
let uniform_step_name = "ustep"
let box_name = "box"
let unbox_name = "unbox"
let push_name = "push"
let pop_name = "pop"
let ceq_name = "ceq"
let copy_name = "copy"
let max_name = "max"

let op_name name =
  let table =
    [
      "(+)", "add";
      "(-)", "sub";
      "(*)", "mult";
      "(/)", "div";
      "(+.)", "fadd";
      "(-.)", "fsub";
      "(*.)", "fmult";
      "(/.)", "fdiv";
      "(=)", "eq";
    ]
  in
  try List.assoc name table with Not_found -> name

let runtime sn = Names.(make_longname (Module runtime_name) sn)

let longname ln =
  let open Names in
  let modn =
    match ln.modn with
    | LocalModule -> Interface.get_current_module_name ()
    | Module modn -> modn
  in
  modn ^ "_" ^ ln.shortn

let method_name ln methd = longname ln ^ "_" ^ methd
let builtin_op_name opn = method_name (runtime builtin_name) opn

let mem_name sn = sn ^ "_mem"
let input_name sn = sn ^ "_input"
let output_name sn = sn ^ "_output"

let alloc = runtime_name ^ "_alloc"
let free = runtime_name ^ "_free"

(******************************************************************************)
