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

let print_name fmt id =
  (* TODO mangling *)
  Format.fprintf fmt "%s" id

let print_ident fmt id =
  print_name fmt (Ident.to_string id)

let print_longname fmt ln =
  print_name fmt (C_utils.longname ln)

let rec print_ty_kont k fmt ty =
  match ty with
  | Scal Data_types.Tys_int ->
    Format.fprintf fmt "int%a" k ()
  | Scal Data_types.Tys_float ->
    Format.fprintf fmt "float%a" k ()
  | Scal Data_types.Tys_bool ->
    Format.fprintf fmt "bool%a" k ()
  | Scal (Data_types.Tys_user ln) ->
    Format.fprintf fmt "%a%a"
      print_longname ln
      k ()
  | Pointer ty ->
    print_ty_kont (fun fmt () -> Format.fprintf fmt "*%a" k ()) fmt ty
  | Array (ty, size) ->
    print_ty_kont
      (fun fmt () -> Format.fprintf fmt "%a[%a]" k () Int.print size)
      fmt
      ty
  | Struct n ->
    Format.fprintf fmt "struct %a%a"
      print_name n
      k ()
  | Name n ->
    Format.fprintf fmt "%a%a"
      print_name n
      k ()

let print_ty fmt ty = print_ty_kont (fun _ () -> ()) fmt ty

let rec print_const_exp fmt ce =
  match ce with
  | Const c ->
    Ast_misc.print_const fmt c
  | Array_lit a ->
    Format.fprintf fmt "((const int[]){@[%a@]})"
      (Utils.print_list_r print_const_exp ",") a
  | Sizeof ty ->
    Format.fprintf fmt "sizeof(%a)"
      print_ty ty

let rec print_lvalue fmt lv =
  match lv with
  | Var (_, id) ->
    print_ident fmt id
  | Index (lv, e) ->
    Format.fprintf fmt "%a[%a]"
      print_lvalue lv
      print_exp e
  | Field (lv, f) ->
    Format.fprintf fmt "%a.%a"
      print_lvalue lv
      print_ident f
  | Deref lv ->
    Format.fprintf fmt "(*%a)"
      print_lvalue lv

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
  | Call (n, e_l) ->
    Format.fprintf fmt "%a(@[%a@])"
      print_name n
      (Utils.print_list_r print_exp ",") e_l
  | AddrOf lv ->
    Format.fprintf fmt "&(%a)"
      print_lvalue lv

let print_var_dec fmt vd =
  Format.fprintf fmt "@[%a"
    (print_ty_kont
       (fun fmt () -> Format.fprintf fmt " %a" Ident.print vd.v_name))
    vd.v_type
  ;
  (
    match vd.v_init with
    | None ->
      ()
    | Some ce ->
      Format.fprintf fmt " =@ %a"
        print_exp ce
  );
  Format.fprintf fmt "@]"

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
    Format.fprintf fmt "@[<v>@[<v>switch (%a) {@ %a@]@ }@]"
      print_exp e
      (Utils.print_list_r print_case "") c_l
  | If (c, t, e) ->
    Format.fprintf fmt "@[<v>@[<v 2>if (%a)@ %a@]@ @[<v 2>else@ %a@]@]"
      print_exp c
      print_stm t
      print_stm e
  | For (v, init, test, step, body) ->
    Format.fprintf fmt
      "@[<v>for (unsigned int %a = %a; %a; %a = %a + %a)@ %a@]"
      Ident.print v
      print_exp init
      print_exp test
      Ident.print v
      Ident.print v
      print_exp step
      print_stm body
  | Return e ->
    Format.fprintf fmt "return %a;"
      print_exp e
  | Block block ->
    print_block fmt block

and print_block fmt block =
  Format.fprintf fmt "@[@[<v 2>{@ %a%a@]@ }@]"
    (Utils.print_list_sep print_var_dec ";") block.b_locals
    (Utils.print_list_r print_stm "") block.b_body

let print_ty_option fmt tyo =
  match tyo with
  | None -> Format.fprintf fmt "void"
  | Some ty -> print_ty fmt ty

let print_fdef fmt fd =
  Format.fprintf fmt "@[%a %a(@[%a@])@ %a@]"
    print_ty_option fd.f_output
    print_name fd.f_name
    (Utils.print_list_r print_var_dec ",") fd.f_input
    print_block fd.f_body

let print_sdef fmt sd =
  Format.fprintf fmt "@[<v 2>struct %a {@ %a@]@ };@]"
    print_name sd.s_name
    (Utils.print_list_sep_r print_var_dec ";") sd.s_fields

let print_edef fmt ed =
  Format.fprintf fmt "@[<v 2>enum %a {@ %a@]@ }@]"
    print_name ed.e_name
    (Utils.print_list_r print_name ",") ed.e_tags

let print_def fmt def =
  match def with
  | Df_function fd ->
    print_fdef fmt fd
  | Df_struct sd ->
    print_sdef fmt sd
  | Df_enum ed ->
    print_edef fmt ed
  | Df_static vd ->
    Format.fprintf fmt "@[static %a;@]"
      print_var_dec vd

let print_fdecl fmt fd =
  Format.fprintf fmt "%a %a(@[%a@]);"
    print_ty_option fd.d_output
    print_name fd.d_name
    (Utils.print_list_r print_ty ",") fd.d_input

let print_decl fmt decl =
  match decl with
  | Dc_function fd ->
    print_fdecl fmt fd
  | Dc_struct id ->
    Format.fprintf fmt "struct %a;" print_name id

let print_phr fmt phr =
  (
    match phr with
    | Def def ->
      print_def fmt def
    | Decl decl ->
      print_decl fmt decl
  );
  Format.fprintf fmt "@\n"

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
  if file.f_kind = Header
  then Format.fprintf fmt "#endif@\n"
