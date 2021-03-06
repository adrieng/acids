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

  type clock_exp_info =
      <
        ci_data : Data_types.data_ty_scal;
        ci_const : Const_types.ty_scal;
      >
  let print_clock_exp_info fmt cei =
    Format.fprintf fmt "%a%a"
      Data_types.print_ty_scal_ann cei#ci_data
      Const_types.print_ty_scal_ann cei#ci_const

  type const_exp_info =
      <
        pwi_data : Data_types.data_ty_scal;
        pwi_const : Const_types.ty_scal;
      >
  let print_const_exp_info fmt (pwi : const_exp_info) =
    Format.fprintf fmt "%a%a"
      Data_types.print_ty_scal_ann pwi#pwi_data
      Const_types.print_ty_scal_ann pwi#pwi_const

  type 'a const_exp_desc = 'a Acids_scoped.Info.const_exp_desc
  let print_const_exp_desc = Acids_scoped.Info.print_const_exp_desc
  let map_const_exp_desc = Acids_scoped.Info.map_const_exp_desc

  type exp_info =
      <
        ei_data : Data_types.data_ty;
        ei_const : Const_types.ty;
      >
  let print_exp_info fmt ei =
    Data_types.print_ty_ann fmt ei#ei_data;
    Const_types.print_ty_ann fmt ei#ei_const

  type app_info = { ai_is_const : bool; }
  let print_app_info fmt { ai_is_const = b; } =
    if !Compiler_options.print_const_info || !Compiler_options.print_all_info
    then Format.fprintf fmt " constity: %b" b

  type block_info = unit
  let print_block_info (_ : Format.formatter) _ = ()

  type pat_info =
      <
        pi_data : Data_types.data_ty;
        pi_const : Const_types.ty;
      >
  let print_pat_info fmt pi =
    Data_types.print_ty_ann fmt pi#pi_data;
    Const_types.print_ty_ann fmt pi#pi_const

  type eq_info = unit
  let print_eq_info (_ : Format.formatter) _ = ()

  type node_info =
      <
        ni_ctx : Ident.ctx;
        ni_data : Data_types.data_sig;
        ni_const : Const_types.ty_sig;
      >
  let print_node_info fmt ni =
    Format.fprintf fmt "%a%a"
      Data_types.print_sig_ann ni#ni_data
      Const_types.print_sig_ann ni#ni_const

  type domain_info = unit
  let print_domain_info (_ : Format.formatter) _ = ()

  type buffer_info = unit
  let print_buffer_info (_ : Format.formatter) _ = ()
end

module M = Acids.Make(Info)
include M

module P = Acids_printer.Make(M)
include P
