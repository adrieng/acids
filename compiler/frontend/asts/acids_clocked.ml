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

type block_free_var_info =
  {
    external_clock : Clock_types.clock_type;
    internal_clock : Clock_types.clock_type;
  }

module Info =
struct
  type var = Ident.t
  let print_var = Ident.print

  type clock_exp_info =
      <
        ci_data : Data_types.data_ty_scal;
        ci_bounds : Interval.t;
        ci_specs : Ast_misc.spec list;
        ci_clock : Clock_types.stream_type;
      >
  let print_clock_exp_info fmt (cei : clock_exp_info) =
    Format.fprintf fmt "@[%a%a%a%a@]"
      Data_types.print_ty_scal_ann cei#ci_data
      Ast_misc.print_interval_annot cei#ci_bounds
      (Utils.print_list Ast_misc.print_spec_annot) cei#ci_specs
      Clock_types.print_stream_type_ann cei#ci_clock

  type const_exp_info =
      <
        pwi_data : Data_types.data_ty_scal;
        pwi_clock : Clock_types.stream_type;
      >
  let print_const_exp_info fmt (pwi : const_exp_info) =
    Format.fprintf fmt "%a%a"
      Data_types.print_ty_scal_ann pwi#pwi_data
      Clock_types.print_stream_type_ann pwi#pwi_clock

  type 'a const_exp_desc = 'a Acids_spec.Info.const_exp_desc
  let print_const_exp_desc = Acids_spec.Info.print_const_exp_desc
  let map_const_exp_desc = Acids_spec.Info.map_const_exp_desc

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
      ai_stream_inst : (int * Clock_types.stream_type) list;
    >
  let print_app_info fmt ci =
    let open Clock_types in
    let print_stream_inst fmt (i, ty) =
      Format.fprintf fmt "%a / %a"
        Clock_types.print_stream_type (St_var i)
        Clock_types.print_stream_type ty
    in
    Format.fprintf fmt " [%a]"
      (Utils.print_list_r print_stream_inst ",") ci#ai_stream_inst

  type block_info = unit
  let print_block_info (_ : Format.formatter) (_ : block_info) = ()

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

  type domain_info =
    <
      di_activation_clock : Clock_types.stream_type;
      di_downsampled : block_free_var_info Ident.Env.t;
    >
  let print_domain_info fmt (info : domain_info) =
    let print_binding fmt { external_clock = ext; internal_clock = int; } =
      Format.fprintf fmt "@[%a down %a = %a@]"
        Clock_types.print_clock_type ext
        Clock_types.print_stream_type info#di_activation_clock
        Clock_types.print_clock_type int
    in
    Format.fprintf fmt "@[%a@]"
      (Ident.Env.print print_binding ";") info#di_downsampled

  type buffer_info =
    <
      bui_is_delay : bool;
      bui_real_size : Int.t;
      bui_size : Int.t;
    >
  let print_buffer_info fmt bu =
    Format.fprintf fmt " %sdelay, size %a (%a)"
      (if bu#bui_is_delay then "" else "not-")
      Int.print bu#bui_size
      Int.print bu#bui_real_size

  type node_info =
      <
        ni_ctx : Ident.ctx;
        ni_data : Data_types.data_sig;
        ni_const : Const_types.ty_sig;
        ni_clock : Clock_types.clock_sig;
      >
  let print_node_info fmt ni =
    Data_types.print_sig_ann fmt ni#ni_data;
    Const_types.print_sig_ann fmt ni#ni_const;
    Clock_types.print_sig_ann fmt ni#ni_clock
end

module M = Acids.Make(Info)
include M

module P = Acids_printer.Make(M)
include P
