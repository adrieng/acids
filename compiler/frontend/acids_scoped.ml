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

let print_no_info fmt _ = Format.fprintf fmt "."

module Parsetree_info =
struct
  type var = Ident.t
  let print_var = Ident.print

  type clock_exp_info = unit
  let print_clock_exp_info = print_no_info

  type exp_info = unit
  let print_exp_info = print_no_info

  type app_info = unit
  let print_app_info = print_no_info

  type block_info = unit
  let print_block_info = print_no_info

  type pat_info = unit
  let print_pat_info = print_no_info

  type eq_info = unit
  let print_eq_info = print_no_info

  type node_info = unit
  let print_node_info = print_no_info
end

module Ast = Acids.Make(Parsetree_info)
include Ast

module Printer = Acids_printer.Make(Parsetree_info)
include Printer
