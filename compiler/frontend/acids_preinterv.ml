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
        ci_static : Static_types.static_ty_scal;
      >
  let print_clock_exp_info (_ : Format.formatter) _ = ()

  type exp_info =
      <
        ei_data : Data_types.data_ty;
        ei_static : Static_types.static_ty;
      >
  let print_exp_info (_ : Format.formatter) _ = ()

  type app_info = unit
  let print_app_info (_ : Format.formatter) _ = ()

  type block_info = unit
  let print_block_info (_ : Format.formatter) _ = ()

  type pat_info =
      <
        pi_data : Data_types.data_ty;
        pi_static : Static_types.static_ty;
      >
  let print_pat_info (_ : Format.formatter) _ = ()

  type eq_info = unit
  let print_eq_info (_ : Format.formatter) _ = ()

  type node_info =
      <
        ni_data : Data_types.data_sig;
        ni_static : Static_types.static_sig;
      >
  let print_node_info (_ : Format.formatter) _ = ()
end

module M = Acids.Make(Info)
include M
