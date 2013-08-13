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
        ci_clock : Clock_types.stream_type;
      >
  let print_clock_exp_info fmt (cei : clock_exp_info) =
    Format.fprintf fmt "%a%a"
      Data_types.print_ty_scal_ann cei#ci_data
      Clock_types.print_stream_type_ann cei#ci_clock

  type static_exp_info =
      <
        pwi_data : Data_types.data_ty_scal;
        pwi_clock : Clock_types.stream_type;
      >
  let print_static_exp_info fmt (pwi : static_exp_info) =
    Format.fprintf fmt "%a%a"
      Data_types.print_ty_scal_ann pwi#pwi_data
      Clock_types.print_stream_type_ann pwi#pwi_clock

  type 'a static_exp_desc = 'a Acids_spec.Info.static_exp_desc
  let print_static_exp_desc = Acids_spec.Info.print_static_exp_desc
  let map_static_exp_desc = Acids_spec.Info.map_static_exp_desc

  type exp_info =
      <
        ei_data : Data_types.data_ty;
        ei_clock : Clock_types.clock_type;
      >
  let print_exp_info fmt ei =
    Data_types.print_ty_ann fmt ei#ei_data;
    Clock_types.print_clock_type_ann fmt ei#ei_clock

  type app_info =
    <
      ai_clock_inst : (int * Clock_types.stream_type) list;
    >
  let print_app_info (_ : Format.formatter) _ = () (* TODO *)

  type block_info = unit
  let print_block_info (_ : Format.formatter) _ = ()

  type pat_info =
      <
        pi_data : Data_types.data_ty;
        pi_clock : Clock_types.clock_type;
      >
  let print_pat_info fmt pi =
    Data_types.print_ty_ann fmt pi#pi_data;
    Clock_types.print_clock_type_ann fmt pi#pi_clock

  type eq_info = unit
  let print_eq_info (_ : Format.formatter) _ = ()

  type domain_info = Clock_types.stream_type
  let print_domain_info fmt st =
    Clock_types.print_stream_type_ann fmt st

  type buffer_info =
    <
      bui_is_delay : bool;
    >
  let print_buffer_info fmt bu =
    Format.fprintf fmt " %sdelay"
      (if bu#bui_is_delay then "" else "not-")

  type node_info =
      <
        ni_ctx : Ident.ctx;
        ni_data : Data_types.data_sig;
        ni_static : Static_types.ty_sig;
        ni_clock : Clock_types.clock_sig;
      >
  let print_node_info fmt ni =
    Data_types.print_sig_ann fmt ni#ni_data;
    Static_types.print_sig_ann fmt ni#ni_static;
    Clock_types.print_sig_ann fmt ni#ni_clock
end

module M = Acids.Make(Info)
include M

module P = Acids_printer.Make(M)
include P
