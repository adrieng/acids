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

module Info =
struct
  type var = Ident.t
  let print_var = Ident.print

  type clock_exp_info = unit
  let print_clock_exp_info = Utils.print_nothing

  type const_exp_info = unit
  let print_const_exp_info = Utils.print_nothing

  type 'a const_exp_desc =
  | Se_var of var
  | Se_global of Names.longname
  | Se_econstr of Ast_misc.econstr
  | Se_binop of Names.shortname * 'a * 'a
  let print_const_exp_desc print fmt sed =
    match sed with
    | Se_var s -> Ident.print fmt s
    | Se_global ln -> Names.print_longname fmt ln
    | Se_econstr ec -> Ast_misc.print_econstr fmt ec
    | Se_binop (op, se1, se2) ->
      Format.fprintf fmt "@[%a(@[%a,@ %a@])@]"
        Names.print_shortname op
        print se1
        print se2
  let map_const_exp_desc f sed =
    match sed with
    | Se_var v -> Se_var v
    | Se_global ln -> Se_global ln
    | Se_econstr ec -> Se_econstr ec
    | Se_binop (op, se1, se2) -> Se_binop (op, f se1, f se2)

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
  let print_domain_info = Utils.print_nothing

  type buffer_info = unit
  let print_buffer_info (_ : Format.formatter) _ = ()

  type node_info = Ident.ctx
  let print_node_info = Utils.print_nothing
end

module Ast = Acids.Make(Info)
include Ast

module Printer = Acids_printer.Make(Ast)
include Printer
