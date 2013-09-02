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

  type clock_exp_info = Acids_clocked.Info.clock_exp_info
  let print_clock_exp_info = Acids_clocked.Info.print_clock_exp_info

  type const_exp_info = Acids_clocked.Info.const_exp_info
  let print_const_exp_info = Acids_clocked.Info.print_const_exp_info

  type 'a const_exp_desc = 'a Acids_spec.Info.const_exp_desc
  let print_const_exp_desc = Acids_spec.Info.print_const_exp_desc
  let map_const_exp_desc = Acids_spec.Info.map_const_exp_desc

  type exp_info =
      <
        ei_data : Data_types.data_ty;
        ei_clock : Clock_types.clock_type;
        ei_relevant_deps : bool;
      >
  let print_exp_info fmt ei =
    Data_types.print_ty_ann fmt ei#ei_data;
    Clock_types.print_clock_type_ann fmt ei#ei_clock;
    Ast_misc.print_annot
      Compiler_options.print_causality_info
      "deps"
      Utils.print_bool
      fmt
      ei#ei_relevant_deps

  type app_info = Acids_clocked.Info.app_info
  let print_app_info = Acids_clocked.Info.print_app_info

  type block_info = Acids_clocked.Info.block_info
  let print_block_info = Acids_clocked.Info.print_block_info

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

  type buffer_info = Acids_clocked.Info.buffer_info
  let print_buffer_info = Acids_clocked.Info.print_buffer_info

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
