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

type ty =
| Ty_scal of Data_types.data_ty_scal
| Ty_arr of Data_types.data_ty_scal * Int.t
| Ty_boxed

type var_dec =
  {
    v_name : Ident.t;
    v_type : ty;
    v_loc : Loc.t;
  }

type buff_dec =
  {
    b_name : Ident.t;
    b_type : ty;
    b_size : Int.t;
    b_loc : Loc.t;
  }

type methd_kind =
| Step
| Reset

type call_kind =
| Builtin of Names.longname
| Method of methd_kind * Ident.t

type lvalue =
| Var of Ident.t
| Index of Ident.t * exp

and exp =
| Const of Ast_misc.const
| Lvalue of lvalue
| Pop of Ident.t * exp (* buffer * amount *)
| Call of call_kind * exp list
| Box of exp list
| Unbox of exp

type stm =
| Skip
| Affect of lvalue * exp
| Push of Ident.t * exp * exp (* buffer * amount * data *)

| Reset of Ident.t

| Switch of exp * (Ast_misc.econstr * stm) list
| For of var_dec * exp * Int.t * stm
(* index * number of iterations * bound * body *)
| Block of block

and block =
  {
    b_locals : var_dec list;
    b_body : stm list;
  }

type methd =
  {
    m_kind : methd_kind;
    m_inputs : var_dec list;
    m_outputs : var_dec list;
    m_body : block;
  }

type machine =
  {
    m_name : Names.longname;
    m_mem : buff_dec list;
    m_methods : methd list;
  }

type file =
  {
    f_name : Names.shortname;
    f_type_defs : Ast_misc.type_def list;
    f_machines : machine list;
  }
