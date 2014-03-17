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

type ident = string

type ty =
| Int
| Float
| Bool
| Pointer of ty
| Array of ty * Int.t
| Struct of string
| Name of string

type var_dec =
  {
    v_name : ident;
    v_type : ty;
  }

type const_exp =
| Const of Ast_misc.const
| Array_lit of const_exp list

type lvalue =
| Var of ident
| Index of ident * exp
| Field of ident * ident
| Deref of ident

and exp =
| ConstExp of const_exp
| Lvalue of lvalue
| Op of string * exp list
| Call of string * exp list
| AddrOf of lvalue

type stm =
| Exp of exp
| Affect of lvalue * exp
| Switch of exp * (Ast_misc.econstr * stm) list
| For of stm * exp * stm * stm
| Block of block

and block =
  {
    b_locals : var_dec list;
    b_body : stm list;
  }

type fdef =
  {
    f_name : ident;
    f_output : ty option;
    f_input : var_dec list;
    f_body : block;
  }

type sdef =
  {
    s_name : ident;
    s_fields : var_dec list;
  }

type edef =
  {
    e_name : ident;
    e_tags : ident list;
  }

type def =
| Df_function of fdef
| Df_struct of sdef
| Df_enum of edef
| Df_static of var_dec * const_exp

type fdecl =
  {
    d_name : ident;
    d_output : ty option;
    d_input : ty list;
  }

type decl =
| Dc_function of fdecl
| Dc_struct of ident

type phr =
| Def of def
| Decl of decl

type file_kind =
| Source
| Header

type file =
  {
    f_name : ident;
    f_kind : file_kind;
    f_includes : string list;
    f_body : phr list;
  }
