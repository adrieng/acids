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

let print_classname fmt ln =
  let print_modul fmt modn =
    match modn with
    | Names.LocalModule ->
      Format.fprintf fmt "LOCAL"
    | Names.Module modn ->
      Names.print_modname fmt modn
  in
  Format.fprintf fmt "%a:%a"
    print_modul ln.Names.modn
    Names.print_shortname ln.Names.shortn

let rec print_ty fmt ty =
  match ty with
  | Ty_mach mty ->
    print_machine_ty fmt mty
  | Ty_scal tys ->
    Data_types.print_ty_scal fmt tys
  | Ty_arr (ty, size) ->
    Format.fprintf fmt "%a^%a"
      print_ty ty
      Int.print size
  | Ty_struct ln ->
    Format.fprintf fmt "struct<%a>"
      Names.print_longname ln

and print_machine_ty fmt mty =
  Format.fprintf fmt "%a%a"
    print_classname mty.mt_name
    (Utils.print_list_r_ne print_const "," "<" ">") mty.mt_cparams

and print_const fmt cst =
  match cst.c_desc with
  | C_scal c ->
    Ast_misc.print_const fmt c
  | C_array arr ->
    Utils.print_list_r_ne print_const "," "[" "]" fmt arr
  | C_sizeof ty ->
    Format.fprintf fmt "sizeof(%a)"
      print_ty ty

let print_var_dec fmt v =
  Format.fprintf fmt "%a@ : %a"
    Ident.print v.v_name
    print_ty v.v_type

let print_var_kind fmt kind =
  match kind with
  | K_input ->
    Format.fprintf fmt "input."
  | K_output ->
    Format.fprintf fmt "output."
  | K_local ->
    ()
  | K_field ->
    Format.fprintf fmt "field."

let rec print_lvalue fmt lv =
  match lv.l_desc with
  | L_var (ty, kind, x) ->
    Format.fprintf fmt "(%a%a : %a)"
      print_var_kind kind
      Ident.print x
      print_ty ty
  | L_arrindex (lv, e) ->
    Format.fprintf fmt "%a[%a]"
      print_lvalue lv
      print_exp e

and print_exp fmt e =
  match e.e_desc with
  | E_lval lv ->
    print_lvalue fmt lv
  | E_const c ->
    print_const fmt c

let print_call fmt call =
  let print_inst fmt inst =
    Format.fprintf fmt "%a :@ "
      print_lvalue inst
  in
  Format.fprintf fmt "@[(@[%a%a@])@,.%a(@[%a@])(@[%a@])@]"
    (Utils.print_opt print_inst) call.c_inst
    print_machine_ty call.c_mach
    Names.print_shortname call.c_method
    (Utils.print_list_r print_exp ",") call.c_inputs
    (Utils.print_list_r print_lvalue ",") call.c_outputs

let rec print_stm fmt stm =
  match stm with
  | S_create (mty, lv) ->
    Format.fprintf fmt "create (%a@ : %a)"
      print_lvalue lv
      print_machine_ty mty
  | S_destroy (mty, lv) ->
    Format.fprintf fmt "destroy (%a@ : %a)"
      print_lvalue lv
      print_machine_ty mty
  | S_call call ->
    print_call fmt call
  | S_affect (lv, e) ->
    Format.fprintf fmt "@[%a@ =@ %a@]"
      print_lvalue lv
      print_exp e
  | S_loop (i, stop, max, body) ->
    Format.fprintf fmt "@[<v>for %a = 0 to max(%a, %a)@ %a@]"
      Ident.print i
      print_exp stop
      Int.print max
      print_stm body
  | S_switch (cond, cases) ->
    let print_case fmt (ec, stm) =
      Format.fprintf fmt "@[<v 2>case %a:@ %a@]"
        Ast_misc.print_econstr ec
        print_stm stm
    in
    Format.fprintf fmt "@[<v>@[<v 2>switch %a {@ %a@]@ }@]"
      print_exp cond
      (Utils.print_list_eol print_case) cases
  | S_if (c, t, e) ->
    Format.fprintf fmt "@[<v>@[<v 2>if (%a)@ %a@]@ @[<v 2>else@ %a@]@]"
      print_exp c
      print_stm t
      print_stm e
  | S_block block ->
    print_block fmt block

and print_block fmt block =
  Format.fprintf fmt "@[<v>@[<v 2>{@ %a%a@]@ }@]"
    (Utils.print_list_sep print_var_dec ";") block.b_locals
    (Utils.print_list_r print_stm ";") block.b_body

let print_methd fmt m =
  Format.fprintf fmt
    "@[<v 2>method %a@ inputs:(@[%a@])@ outputs:(@[%a@])@ %a@]"
    Names.print_shortname m.m_name
    (Utils.print_list_r print_var_dec " *") m.m_inputs
    (Utils.print_list_r print_var_dec " *") m.m_outputs
    print_block m.m_body

let print_machine fmt m =
  Format.fprintf fmt
    "@[@[<v 2>machine %a {@\n%a@\n@[<v>@[<v 2>constructor {@ %a@]@ }@]@\n@[<v>@[<v 2>destructor {@ %a@]@ }@]@\n%a@]@\n}@]"
    Names.print_longname m.ma_name
    (Utils.print_list_eol print_var_dec) m.ma_fields
    (Utils.print_list_r print_stm ";") m.ma_constructor
    (Utils.print_list_r print_stm ";") m.ma_destructor
    (Utils.print_list_eol print_methd) m.ma_methods

let print_user_type_def fmt td =
  let open Ast_misc in
  Format.fprintf fmt "@[<v 2>type %a =@ %a@]"
    Names.print_shortname td.ty_name
    (Utils.print_list_r Names.print_shortname "|") td.ty_body

let print_type_def fmt td =
  match td with
  | Td_user td ->
    print_user_type_def fmt td
  | Td_struct (name, fields) ->
    Format.fprintf fmt "@[<v>@[<v 2>type %a =@ { %a@]@ }@]"
      Names.print_shortname name
      (Utils.print_list_r print_var_dec ",") fields

let print_file fmt file =
  Format.fprintf fmt "@[(* File %a *)@\n%a@\n%a@\n@]"
    Names.print_shortname file.f_name
    (Utils.print_list_eol print_type_def) file.f_type_defs
    (Utils.print_list_eol print_machine) file.f_machines
