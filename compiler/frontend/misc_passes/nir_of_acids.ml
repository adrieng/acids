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

open Acids_causal

let do_file ctx (file : Acids_causal_utils.annotated_file) =
  let nir_file : unit Nir.file =
    {
      Nir.f_name = file.f_name;
      Nir.f_interfaces = file.f_info#interfaces;
      Nir.f_type_defs = [];
      Nir.f_body = [];
    }
  in
  ctx, nir_file

let pass =
  let open Pass_manager in
  P_transform
    (make_transform
       ~ext:"nir"
       ~print_out:Nir_printer.print_file
       "nir_of_acids"
       do_file)
