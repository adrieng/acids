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
        ci_interv : Interval.t;
        ci_static : Static_types.ty_scal;
      >
  let print_clock_exp_info fmt cei =
    Format.fprintf fmt ": %a in %a is %a"
      Data_types.print_data_ty_scal cei#ci_data
      Interval.print cei#ci_interv
      Static_types.print_static_ty_scal cei#ci_static

  type exp_info =
      <
        ei_data : Data_types.data_ty;
        ei_interv : Interval_types.ty;
        ei_static : Static_types.ty;
      >
  let print_exp_info fmt ei =
    Format.fprintf fmt ": %a"
      Data_types.print_ty ei#ei_data;
    if ei#ei_interv <> Interval_types.It_scal Interval_types.Is_top
    then Format.fprintf fmt " in %a" Interval_types.print_ty ei#ei_interv;
    Format.fprintf fmt " is %a" Static_types.print_static_ty ei#ei_static

  type app_info = unit
  let print_app_info (_ : Format.formatter) _ = ()

  type block_info = unit
  let print_block_info (_ : Format.formatter) _ = ()

  type pat_info =
      <
        pi_data : Data_types.data_ty;
        pi_interv : Interval_types.ty;
        pi_static : Static_types.ty;
      >
  let print_pat_info fmt pi =
    Format.fprintf fmt ": %a"
      Data_types.print_ty pi#pi_data;
    if pi#pi_interv <> Interval_types.It_scal Interval_types.Is_top
    then Format.fprintf fmt " in %a" Interval_types.print_ty pi#pi_interv;
    Format.fprintf fmt " is %a" Static_types.print_static_ty pi#pi_static

  type eq_info = unit
  let print_eq_info (_ : Format.formatter) _ = ()

  type node_info =
      <
        ni_data : Data_types.data_sig;
        ni_interv : Interval_types.ty_sig;
        ni_static : Static_types.ty_sig;
      >
  let print_node_info fmt ni =
    Format.fprintf fmt ": %a in %a is %a"
      Data_types.print_sig ni#ni_data
      Interval_types.print_sig ni#ni_interv
      Static_types.print_sig ni#ni_static

  type domain_info = unit
  let print_domain_info (_ : Format.formatter) _ = ()
end

module M = Acids.Make(Info)
include M

module P = Acids_printer.Make(M)
include P
