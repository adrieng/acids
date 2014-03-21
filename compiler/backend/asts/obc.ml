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
| Ty_mach of machine_ty
| Ty_scal of Data_types.data_ty_scal
| Ty_arr of ty * Int.t
| Ty_struct of Names.longname

and machine_ty =
  {
    mt_name : Names.longname;
    mt_cparams : const list;
  }

and const =
  {
    c_desc : const_desc;
    c_type : ty;
  }

and const_desc =
| C_scal of Ast_misc.const
| C_array of const list
| C_sizeof of ty

type var_dec =
  {
    v_name : Ident.t;
    v_type : ty;
    v_loc : Loc.t;
  }

type var_kind =
| K_input
| K_output
| K_local
| K_field

type lvalue =
  {
    l_desc : lvalue_desc;
    l_type : ty;
  }

and lvalue_desc =
| L_var of var_kind * Ident.t
| L_arrindex of lvalue * exp

and exp =
  {
    e_desc : exp_desc;
    e_type : ty;
  }

and exp_desc =
| E_lval of lvalue
| E_const of const

type call =
  {
    c_inst : lvalue option;
    c_mach : machine_ty;
    c_method : Names.shortname;
    c_inputs : exp list;
    c_outputs : lvalue list;
  }

type stm =
| S_create of machine_ty * lvalue
| S_destroy of machine_ty * lvalue
| S_affect of lvalue * exp
| S_call of call
| S_loop of Ident.t * exp * Int.t * stm (* for v = 0 to max(exp, n) do body *)
| S_switch of exp * (Ast_misc.econstr * stm) list
| S_if of exp * stm * stm
| S_block of block

and block =
  {
    b_locals : var_dec list;
    b_body : stm list;
  }

type methd =
  {
    m_name : Names.shortname;
    m_inputs : var_dec list;
    m_outputs : var_dec list;
    m_body : block;
  }

type machine =
  {
    ma_name : Names.longname;
    ma_ctx : Ident.ctx;
    ma_fields : var_dec list;
    ma_constructor : stm list;
    ma_destructor : stm list;
    ma_methods : methd list;
  }

type type_def =
  | Td_user of Ast_misc.type_def
  | Td_struct of Names.shortname * var_dec list

type file =
  {
    f_name : Names.shortname;
    f_type_defs : type_def list;
    f_machines : machine list;
  }
