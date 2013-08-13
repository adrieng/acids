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

module Info =
struct
  type var = string
  let print_var fmt s = Format.fprintf fmt "%s" s

  type clock_exp_info = unit
  let print_clock_exp_info = Utils.print_nothing

  type static_exp_info = unit
  let print_static_exp_info = Utils.print_nothing

  type 'a static_exp_desc =
  | Se_var of var
  | Se_econstr of Ast_misc.econstr
  | Se_fword of Int.t list
  let print_static_exp_desc _ fmt sed =
    match sed with
    | Se_var s -> Format.fprintf fmt "%s" s
    | Se_econstr ec -> Ast_misc.print_econstr fmt ec
    | Se_fword i_l -> Format.fprintf fmt "'%a'" (Utils.print_list Int.print) i_l
  let map_static_exp_desc _ sed =
    match sed with
    | Se_var v -> Se_var v
    | Se_econstr ec -> Se_econstr ec
    | Se_fword i_l -> Se_fword i_l

  type exp_info = unit
  let print_exp_info = Utils.print_nothing

  type app_info = unit
  let print_app_info = Utils.print_nothing

  type block_info = unit
  let print_block_info = Utils.print_nothing

  type pat_info = unit
  let print_pat_info = Utils.print_nothing

  type eq_info = unit
  let print_eq_info = Utils.print_nothing

  type domain_info = unit
  let print_domain_info _ () = ()

  type buffer_info = unit
  let print_buffer_info (_ : Format.formatter) _ = ()

  type node_info = unit
  let print_node_info = Utils.print_nothing
end

module Ast = Acids.Make(Info)
include Ast

module Printer = Acids_printer.Make(Ast)
include Printer
