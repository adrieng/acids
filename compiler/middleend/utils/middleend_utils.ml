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

module Make(A : Nir.A)(B : Nir.A) =
struct
  module P = Nir_printer.Make(B)

  let map_to_nodes f_node ctx (file : Interface.env A.file) =
    ctx,
    {
      B.f_name = file.A.f_name;
      B.f_type_defs = file.A.f_type_defs;
      B.f_body = List.map f_node file.A.f_body;
      B.f_info = file.A.f_info;
    }

  let make_transform name tr =
    let open Pass_manager in
    P_transform
      (make_transform
         ~ext:"nir"
         ~print_out:P.print_file
         (* ~guarantee:Nir_invariants.all *)
         name
         tr)
end
