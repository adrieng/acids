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

open C

let longname ln =
  let open Names in
  let modn =
    match ln.modn with
    | LocalModule ->
      Interface.get_current_module_name ()
    | Module modn ->
      modn
  in
  modn ^ "_" ^ ln.shortn

let fun_decl_of_fun_def (f : fdef) =
  {
    d_name = f.f_name;
    d_output = f.f_output;
    d_input = List.map (fun v -> v.v_type) f.f_input;
  }

let int_ty = Scal Data_types.Tys_int
let int i = ConstExp (Const Ast_misc.(Cconstr (Ec_int i)))
