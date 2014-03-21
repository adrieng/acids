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

open Obc

let make_const_scal ty c =
  {
    c_desc = C_scal c;
    c_type = ty;
  }

let make_const_econstr tys ec =
  make_const_scal (Ty_scal tys) (Ast_misc.Cconstr ec)

let make_const_int i =
  make_const_econstr Data_types.Tys_int (Ast_misc.Ec_int i)

let make_const_array c_l =
  let c = Utils.assert1 c_l in
  {
    c_desc = C_array c_l;
    c_type = Ty_arr (c.c_type, Int.of_int (List.length c_l));
  }

let make_const_sizeof ty =
  {
    c_desc = C_sizeof ty;
    c_type = Ty_scal Data_types.Tys_int;
  }

let make_exp_const c =
  {
    e_desc = Obc.E_const c;
    e_type = c.c_type;
  }

let make_exp_lvalue lv =
  {
    e_desc = Obc.E_lval lv;
    e_type = lv.l_type;
  }

let make_exp_int i =
  make_exp_const (make_const_int i)
