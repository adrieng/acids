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

let print_ident fmt id =
  (* TODO mangling *)
  Format.fprintf fmt "%s" id

let rec print_ty fmt ty =
  match ty with
  | Int ->
    Format.fprintf fmt "int"
  | Float ->
    Format.fprintf fmt "float"
  | Bool ->
    Format.fprintf fmt "bool"
  | Pointer ty ->
    Format.fprintf fmt "%a*"
      print_ty ty
  | Array (ty, size) ->
    Format.fprintf fmt "%a[%a]"
      print_ty ty
      Int.print size
  | Struct id ->
    Format.fprintf fmt "struct %a"
      print_ident id
  | Name id ->
    print_ident fmt id

let print_var_dec fmt vd =
  Format.fprintf fmt "%a %a"
    print_ty vd.v_type
    print_ident vd.v_name

let rec print_const_exp fmt ce =
  match ce with
  | Const c ->
    Ast_misc.print_const fmt c
  | Array_lit a ->
    Utils.print_list_r_ne print_const_exp "," "{" "}" fmt a

let rec print_lvalue fmt lv =
  match lv with
  | Var id ->
    print_ident fmt id
  | Index (id, e) ->
    Format.fprintf fmt "%a[%a]"
      print_ident id
      print_exp e
  | Field (s, f) ->
    Format.fprintf fmt "%a.%a"
      print_ident s
      print_ident f
  | Deref id ->
    Format.fprintf fmt "*%a"
      print_ident id

and print_exp fmt e =
  match e with
  | ConstExp ce ->
    print_const_exp fmt ce
  | Lvalue lv ->
    print_lvalue fmt lv
  | Op (s, [e1; e2]) ->
    Format.fprintf fmt "(@[%a %s@ %a@])"
      print_exp e1
      s
      print_exp e2
  | Op (s, e_l) ->
    Format.fprintf fmt "%s(@[%a@])"
      s
      (Utils.print_list_r print_exp ",") e_l
  | Call (fn, e_l) ->
    Format.fprintf fmt "%a(@[%a@])"
      print_ident fn
      (Utils.print_list_r print_exp ",") e_l
  | AddrOf lv ->
    Format.fprintf fmt "&%a"
      print_lvalue lv

let rec print_stm fmt stm =
  match stm with
  | Exp e ->
    Format.fprintf fmt "%a;"
      print_exp e
  | Affect (lv, e) ->
    Format.fprintf fmt "%a = %a;"
      print_lvalue lv
      print_exp e
  | Switch (e, c_l) ->
    let print_case fmt (ec, stm) =
      Format.fprintf fmt "@[<v 2>case %a:@ %a@ break;@]"
        Ast_misc.print_econstr ec
        print_stm stm
    in
    Format.fprintf fmt "@[@[<v>switch (%a) {@ %a@]@ }@]"
      print_exp e
      (Utils.print_list print_case) c_l
  | For (init, test, step, body) ->
    Format.fprintf fmt "@[@[<v>for (%a; %a; %a) {@ %a@]@ }@]"
      print_stm init
      print_exp test
      print_stm step
      print_stm body
  | Block block ->
    print_block fmt block

and print_block fmt block =
  Format.fprintf fmt "@[@[<v 2>{@ %a%a@]@ }@]"
    (Utils.print_list_eol print_var_dec) block.b_locals
    (Utils.print_list_r print_stm "") block.b_body

let print_ty_option fmt tyo =
  match tyo with
  | None -> Format.fprintf fmt "void"
  | Some ty -> print_ty fmt ty

let print_fdef fmt fd =
  Format.fprintf fmt "@[%a %a(@[%a@])@ %a@]"
    print_ty_option fd.f_output
    print_ident fd.f_name
    (Utils.print_list_r print_var_dec ",") fd.f_input
    print_block fd.f_body

let print_sdef fmt sd =
  Format.fprintf fmt "@[<v 2>struct %a {@ %a@]@ }@]"
    print_ident sd.s_name
    (Utils.print_list_sep_r print_var_dec ";") sd.s_fields

let print_edef fmt ed =
  Format.fprintf fmt "@[<v 2>enum %a {@ %a@]@ }@]"
    print_ident ed.e_name
    (Utils.print_list_r print_ident ",") ed.e_tags

let print_def fmt def =
  match def with
  | Df_function fd ->
    print_fdef fmt fd
  | Df_struct sd ->
    print_sdef fmt sd
  | Df_enum ed ->
    print_edef fmt ed
  | Df_static (vd, ce) ->
    Format.fprintf fmt "@[static const %a =@ %a;@]"
      print_var_dec vd
      print_const_exp ce

let print_fdecl fmt fd =
  Format.fprintf fmt "%a %a(@[%a@]);"
    print_ty_option fd.d_output
    print_ident fd.d_name
    (Utils.print_list_r print_ty ",") fd.d_input

let print_decl fmt decl =
  match decl with
  | Dc_function fd ->
    print_fdecl fmt fd
  | Dc_struct id ->
    Format.fprintf fmt "struct %a;" print_ident id

let print_phr fmt phr =
  match phr with
  | Def def ->
    print_def fmt def
  | Decl decl ->
    print_decl fmt decl

let print_file_kind fmt kind =
  match kind with
  | Source ->
    Format.fprintf fmt "Source"
  | Header ->
    Format.fprintf fmt "Header"

let print_file fmt file =
  Format.fprintf fmt "// %a file for AcidS module %s@\n"
    print_file_kind file.f_kind
    file.f_name;
  let guard = String.uppercase file.f_name ^ "_H" in
  if file.f_kind = Header
  then Format.fprintf fmt "#ifndef %s@\n#define %s@\n@\n" guard guard;
  List.iter
    (fun s -> Format.fprintf fmt "#include \"%s.h\"@\n" s)
    file.f_includes;
  Format.fprintf fmt "@\n";
  Utils.print_list_eol print_phr fmt file.f_body;
  Format.fprintf fmt "@\n";
  if file.f_kind = Header
  then Format.fprintf fmt "#endif@\n"
