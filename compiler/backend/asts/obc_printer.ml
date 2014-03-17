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

let rec print_ty fmt ty =
  match ty with
  | Ty_scal tys ->
    Data_types.print_ty_scal fmt tys
  | Ty_arr (ty, size) ->
    Format.fprintf fmt "%a^%a"
      print_ty ty
      Int.print size
  | Ty_boxed ->
    Format.fprintf fmt "boxed"

let print_inst_kind fmt kind =
  match kind with
  | Mach ln ->
    Names.print_longname fmt ln
  | Pword p ->
    Ast_misc.print_const_pword fmt p
  | Buffer (ty, size) ->
    Format.fprintf fmt "buffer<%a>(%a)"
      Int.print size
      print_ty ty

let print_inst fmt inst =
  Format.fprintf fmt "inst %a: %a"
    Ident.print inst.i_name
    print_inst_kind inst.i_kind

let print_var_dec fmt v =
  Format.fprintf fmt "%a : %a"
    Ident.print v.v_name
    print_ty v.v_type

let print_methd_kind fmt meth =
  match meth with
  | Step -> Format.fprintf fmt "step"
  | Reset -> Format.fprintf fmt "reset"

let print_call_kind fmt kind =
  match kind with
  | Builtin id ->
    Names.print_shortname fmt id
  | Method (kind, id) ->
    Format.fprintf fmt "%a.%a"
      Ident.print id
      print_methd_kind kind
  | Pword id ->
    Format.fprintf fmt "%a.next"
      Ident.print id

let rec print_lvalue fmt lv =
  match lv with
  | Var n ->
    Ident.print fmt n
  | Index (n, e) ->
    Format.fprintf fmt "%a[%a]"
      Ident.print n
      print_exp e

and print_exp fmt e =
  match e with
  | Const c ->
    Ast_misc.print_const fmt c
  | Lvalue lv ->
    print_lvalue fmt lv
  | Pop (id, e) ->
    Format.fprintf fmt "pop(@[%a,@ %a@])"
      Ident.print id
      print_exp e
  | Box e_l ->
    Format.fprintf fmt "box(@[%a])"
      (Utils.print_list_r print_exp ",") e_l
  | Unbox e ->
    Format.fprintf fmt "unbox(@[%a])" print_exp e

let print_call fmt call =
  Format.fprintf fmt "@[%a@,(@[%a@])@,(@[%a@])@]"
    print_call_kind call.c_kind
    (Utils.print_list_r print_exp ",") call.c_inputs
    (Utils.print_list_r print_lvalue ",") call.c_outputs

let rec print_stm fmt stm =
  match stm with
  | Skip ->
    Format.fprintf fmt "skip"
  | Affect (lv, e) ->
    Format.fprintf fmt "@[%a :=@ %a@]"
      print_lvalue lv
      print_exp e
  | Call call ->
    print_call fmt call
  | Pop (id, size, result) ->
    Format.fprintf fmt "push(@[%a, %a, %a@])"
      Ident.print id
      print_exp size
      Ident.print result
  | Push (id, size, data) ->
    Format.fprintf fmt "push(@[%a, %a, %a@])"
      Ident.print id
      print_exp size
      Ident.print data
  | Reset (kind, id)  ->
    Format.fprintf fmt "%a.reset(%a)"
      print_inst_kind kind
      Ident.print id
  | Switch (cond, cases) ->
    let print_case fmt (ec, stm) =
      Format.fprintf fmt "@[<v 2>case %a:@ %a@]"
        Ast_misc.print_econstr ec
        print_stm stm
    in
    Format.fprintf fmt "@[<v>@[<v 2>switch %a {@ %a@]@ }@]"
      print_exp cond
      (Utils.print_list_eol print_case) cases
  | For (v, count, bound, body) ->
    Format.fprintf fmt "@[<v>for %a = 0 to max(%a, %a)@ %a@]"
      print_var_dec v
      print_exp count
      Int.print bound
      print_stm body
  | Block block ->
    print_block fmt block

and print_block fmt block =
  Format.fprintf fmt "@[<v>@[<v 2>{@ %a%a%a@]@ }@]"
    (Utils.print_list_sep print_var_dec ";") block.b_vars
    (Utils.print_list_sep print_inst ";") block.b_insts
    (Utils.print_list_r print_stm ";") block.b_body

let print_methd fmt m =
  let print_prefix pref f fmt x =
    Format.fprintf fmt "%s %a" pref f x
  in
  Format.fprintf fmt
    "@[<v>method %a(@[%a%a@])@ %a@]"
    print_methd_kind m.m_kind
    (Utils.print_list_sep (print_prefix "in" print_var_dec) ",") m.m_inputs
    (Utils.print_list_r (print_prefix "out" print_var_dec) ",") m.m_outputs
    print_block m.m_body

let print_machine fmt m =
  Format.fprintf fmt
    "@[@[<v 2>machine %a {@\n%a@\n%a@]@\n}@]"
    Names.print_longname m.m_name
    (Utils.print_list_eol print_inst) m.m_insts
    (Utils.print_list_eol print_methd) m.m_methods

let print_type_def fmt td =
  let open Ast_misc in
  Format.fprintf fmt "@[<v 2>type %a =@ %a@]"
    Names.print_shortname td.ty_name
    (Utils.print_list_r Names.print_shortname "|") td.ty_body

let print_file fmt file =
  Format.fprintf fmt "@[(* File %a *)@\n%a@\n%a@\n@]"
    Names.print_shortname file.f_name
    (Utils.print_list_eol print_type_def) file.f_type_defs
    (Utils.print_list_eol print_machine) file.f_machines
