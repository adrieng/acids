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
        ci_static : Static_types.ty_scal;
        ci_interv : Interval.t;
        ci_spec : Ast_misc.spec list;
      >
  let print_clock_exp_info fmt cei =
    Format.fprintf fmt "@[%a%a%a%a@]"
      Data_types.print_ty_scal_ann cei#ci_data
      Static_types.print_ty_scal_ann cei#ci_static
      Ast_misc.print_interval_annot cei#ci_interv
      (Utils.print_list_r Ast_misc.print_spec_annot "") cei#ci_spec

  type static_exp_info =
      <
        pwi_data : Data_types.data_ty_scal;
        pwi_static : Static_types.ty_scal;
        pwi_spec : Ast_misc.spec list;
      >
  let print_static_exp_info fmt (pwi : static_exp_info) =
    Format.fprintf fmt "@[%a%a%a@]"
      Data_types.print_ty_scal_ann pwi#pwi_data
      Static_types.print_ty_scal_ann pwi#pwi_static
      (Utils.print_list_r Ast_misc.print_spec_annot "") pwi#pwi_spec

  type static_exp_desc = Ast_misc.econstr
  let print_static_exp_desc fmt ec = Ast_misc.print_econstr fmt ec

  type exp_info =
      <
        ei_data : Data_types.data_ty;
        ei_static : Static_types.ty;
        ei_spec : Ast_misc.spec list;
      >
  let print_exp_info fmt ei =
    Data_types.print_ty_ann fmt ei#ei_data;
    Static_types.print_ty_ann fmt ei#ei_static;
    Utils.print_list_r Ast_misc.print_spec_annot "" fmt ei#ei_spec

  type app_info = unit
  let print_app_info (_ : Format.formatter) _ = ()

  type block_info = unit
  let print_block_info (_ : Format.formatter) _ = ()

  type pat_info =
      <
        pi_data : Data_types.data_ty;
        pi_static : Static_types.ty;
        pi_spec : Ast_misc.spec list;
      >
  let print_pat_info fmt pi =
    Data_types.print_ty_ann fmt pi#pi_data;
    Static_types.print_ty_ann fmt pi#pi_static;
    Utils.print_list_r Ast_misc.print_spec_annot "" fmt pi#pi_spec

  type eq_info = unit
  let print_eq_info (_ : Format.formatter) _ = ()

  type node_info =
      <
        ni_ctx : Ident.ctx;
        ni_data : Data_types.data_sig;
        ni_static : Static_types.ty_sig;
      >
  let print_node_info fmt ni =
    Format.fprintf fmt "%a%a"
      Data_types.print_sig_ann ni#ni_data
      Static_types.print_sig_ann ni#ni_static

  type domain_info = unit
  let print_domain_info (_ : Format.formatter) _ = ()
end

module M = Acids.Make(Info)
include M

module P = Acids_printer.Make(M)
include P
