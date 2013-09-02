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
  type var = Ident.t
  let print_var = Ident.print

  type clock_exp_info =
      <
        ci_data : Data_types.data_ty_scal;
      >
  let print_clock_exp_info fmt cei =
    Data_types.print_ty_scal_ann fmt cei#ci_data

  type const_exp_info =
      <
        pwi_data : Data_types.data_ty_scal;
      >
  let print_const_exp_info fmt (pwi : const_exp_info) =
    Data_types.print_ty_scal_ann fmt pwi#pwi_data

  type 'a const_exp_desc = 'a Acids_scoped.Info.const_exp_desc
  let print_const_exp_desc = Acids_scoped.Info.print_const_exp_desc
  let map_const_exp_desc = Acids_scoped.Info.map_const_exp_desc

  type exp_info =
      <
        ei_data : Data_types.data_ty;
      >
  let print_exp_info fmt ei =
    Data_types.print_ty_ann fmt ei#ei_data

  type app_info = unit
  let print_app_info (_ : Format.formatter) _ = ()

  type block_info = unit
  let print_block_info (_ : Format.formatter) _ = ()

  type pat_info =
      <
        pi_data : Data_types.data_ty;
      >
  let print_pat_info fmt pi =
    Data_types.print_ty_ann fmt pi#pi_data

  type eq_info = unit
  let print_eq_info (_ : Format.formatter) _ = ()

  type domain_info = unit
  let print_domain_info _ () = ()

  type buffer_info = unit
  let print_buffer_info (_ : Format.formatter) _ = ()

  type node_info =
      <
        ni_ctx : Ident.ctx;
        ni_data : Data_types.data_sig;
      >
  let print_node_info fmt ni =
    Data_types.print_sig_ann fmt ni#ni_data
end

module Ast = Acids.Make(Info)
include Ast

module Printer = Acids_printer.Make(Ast)
include Printer
