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
open C_utils

(*
  Things to document:

  * General structure of the code

  * Calling convention

  * Runtime system
*)

(******************************************************************************)
(* {2 Helpers} *)

let mem_struct_name ln =
  Backend_utils.mem_name (Backend_utils.longname ln)
let create_name ln =
  Backend_utils.method_name ln Backend_utils.create_name
let destroy_name ln =
  Backend_utils.method_name ln Backend_utils.destroy_name
let max_name = Backend_utils.builtin_op_name Backend_utils.max_name

let op_add = "+"
let op_lt = "<"

let fun_decl_of_fun_def (fdef : C.fdef) =
  let open C in
  {
    d_name = fdef.f_name;
    d_output = fdef.f_output;
    d_input = List.map (fun vd -> vd.v_type) fdef.f_input;
  }

let mutable_ty ty =
  let open C in
  match ty with
  | Scal _ | Struct _ -> false
  | Pointer _ | Array _ -> true
  | Void -> invalid_arg "mutable_ty: C.Void"
  | Name _ -> invalid_arg "mutable_ty: C.Name"

(******************************************************************************)
(* {2 AST walking} *)

let rec translate_ty ty =
  match ty with
  | Ty_scal Data_types.Tys_bool -> C.Scal Data_types.Tys_int
  | Ty_scal tys -> C.Scal tys
  | Ty_arr (ty, size) -> C.Array (translate_ty ty, size)
  | Ty_mach mty -> C.(Pointer (Struct (mem_struct_name mty.mt_name)))
  | Ty_struct ln -> C.Struct (Backend_utils.longname ln)

let rec translate_const c =
  let cd =
    match c.c_desc with
    | C_scal c ->
      C.Const c
    | C_array a ->
      C.Array_lit (List.map translate_const a)
    | C_sizeof ty ->
      C.Sizeof (translate_ty ty)
  in
  {
    C.c_desc = cd;
    C.c_type = translate_ty c.c_type;
  }

let translate_var_dec vd =
  {
    C.v_name = vd.v_name;
    C.v_type = translate_ty vd.v_type;
    C.v_init = None;
  }

let rec translate_lvalue mem lv =
  let ld, ty =
    match lv.l_desc with
    | L_var ((K_local | K_input), id) ->
      C.Var id, translate_ty lv.l_type
    | L_var (K_output, id) ->
      C.Var id, C.Pointer (translate_ty lv.l_type)
    | L_var (K_field, id) ->
      C.Field (lvalue_deref mem, id), translate_ty lv.l_type
    | L_arrindex (lv, e) ->
      C.Index (translate_lvalue mem lv, translate_exp mem e),
      translate_ty lv.l_type
    | L_field (lv, id) ->
      let slv = translate_lvalue mem lv in
      let slv = if mutable_ty slv.C.l_type then lvalue_deref slv else slv in
      C.Field (slv, id), translate_ty lv.l_type
  in
  {
    C.l_desc = ld;
    C.l_type = ty;
  }

and translate_exp mem e =
  match e.e_desc with
  | E_lval lv -> exp_lvalue (translate_lvalue mem lv)
  | E_const c -> exp_const (translate_const c)

let translate_lvalue_exp mem lv =
  exp_lvalue (translate_lvalue mem lv)

let translate_lvalue_ref mem lv =
  let lv = translate_lvalue mem lv in
  if mutable_ty lv.C.l_type then exp_lvalue lv else exp_addrof lv

let translate_call mem call =
  let translate_exp = translate_exp mem in

  let fun_n = Backend_utils.method_name call.c_mach.mt_name call.c_method in

  let inputs = List.map translate_exp call.c_inputs in
  let outputs = List.map (translate_lvalue_ref mem) call.c_outputs in

  let args = inputs @ outputs in
  let args =
    List.map
      (fun c -> exp_const (translate_const c))
      call.c_mach.mt_cparams
    @ args
  in
  let args =
    match call.c_inst with
    | I_static -> args
    | I_self -> exp_lvalue mem :: args
    | I_var lv -> translate_lvalue_exp mem lv :: args
  in
  C.Exp (exp_void (C.Call (fun_n, args)))

let rec translate_stm mem stm =
  let translate_lvalue = translate_lvalue mem in
  let translate_lvalue_exp = translate_lvalue_exp mem in
  let translate_exp = translate_exp mem in
  let translate_stm = translate_stm mem in

  match stm with
  | S_create (mty, lv) ->
    C.Affect (translate_lvalue lv, exp_call_void (create_name mty.mt_name) [])
  | S_destroy (mty, lv) ->
    C.Exp (exp_call_void (destroy_name mty.mt_name) [translate_lvalue_exp lv])
  | S_affect (lv, e) ->
    C.Affect (translate_lvalue lv, translate_exp e)
  | S_call call ->
    translate_call mem call
  | S_loop (v, stop, bound, body) ->
    let open C in

    let stop =
      exp_op_int op_lt
        [exp_var_int v;
         exp_int (C.Call (max_name, [translate_exp stop; exp_const_int bound]))]
    in

    For
      (
        v,
        exp_const_int Int.zero,
        stop,
        exp_const_int Int.one,
        translate_stm body
      )
  | S_switch (e, cases) ->
    C.Switch
      (
        translate_exp e,
        List.map (fun (ec, stm) -> ec, translate_stm stm) cases
      )
  | S_if (c, t, e) ->
    C.If (translate_exp c, translate_stm t, translate_stm e)
  | S_block block ->
    C.Block (translate_block mem block)

and translate_block mem block =
  {
    C.b_locals = List.map translate_var_dec block.b_locals;
    C.b_body = List.map (translate_stm mem) block.b_body;
  }

let translate_methd mach_name methd =
  let mem = Ident.make_internal "mem" in
  let mem_ty = C.(Pointer (Struct (mem_struct_name mach_name))) in

  let mem_input =
    let open C in
    {
      v_name = mem;
      v_type = mem_ty;
      v_init = None;
    }
  in

  let inputs =
    let add_deref_if_mutable vd =
      let open C in
      let ty = vd.v_type in
      { vd with v_type = if mutable_ty ty then ty else C.Pointer ty; }
    in
    List.map translate_var_dec methd.m_inputs
    @
      List.map
      (fun vd -> add_deref_if_mutable (translate_var_dec vd))
      methd.m_outputs
  in

  let mem_lv =
    {
      C.l_desc = C.Var mem;
      C.l_type = mem_ty;
    }
  in

  {
    C.f_name = Backend_utils.method_name mach_name methd.m_name;
    C.f_output = C.Void;
    C.f_input = if methd.m_static then inputs else mem_input :: inputs;
    C.f_body = translate_block mem_lv methd.m_body;
  }

let translate_machine (source, header) mach =
  Ident.set_current_ctx mach.ma_ctx;

  let mem_def =
    C.Def
      (C.Df_struct
         {
           C.s_name = mem_struct_name mach.ma_name;
           C.s_fields = List.map translate_var_dec mach.ma_fields;
         })
  in

  let mem_decl = C.Decl (C.Dc_struct (mem_struct_name mach.ma_name)) in

  let mem = Ident.make_internal "mem" in
  let mty = C.Struct (mem_struct_name mach.ma_name) in
  let mpty = C.Pointer mty in
  let mem_lv =
    {
      C.l_desc = C.Var mem;
      C.l_type = mpty;
    }
  in

  let constructor =
    let open C in
    let init = exp_int (Call (Backend_utils.alloc, [exp_sizeof mty])) in
    {
      f_name = create_name mach.ma_name;
      f_output = mpty;
      f_input = [];
      f_body =
        {
          b_locals = [{ v_name = mem; v_type = mpty; v_init = Some init; }];
          b_body =
            List.map (translate_stm mem_lv) mach.ma_constructor
            @ [Return (exp_lvalue mem_lv)];
        }
    }
  in

  let destructor =
    let open C in
    let free = C.Exp (exp_call_void Backend_utils.free [exp_lvalue mem_lv]) in
    {
      f_name = destroy_name mach.ma_name;
      f_output = C.Void;
      f_input = [{ v_name = mem; v_type = mpty; v_init = None; }];
      f_body =
        {
          b_locals = [];
          b_body =
            List.map (translate_stm mem_lv) mach.ma_destructor @ [free];
        }
    }
  in

  let fun_defs =
    List.rev_map (translate_methd mach.ma_name) mach.ma_methods
    @ [destructor; constructor]
  in
  let fun_decls = List.map fun_decl_of_fun_def fun_defs in
  let fun_defs = List.map (fun f -> C.(Def (Df_function f))) fun_defs in
  let fun_decls = List.map (fun f -> C.(Decl (Dc_function f))) fun_decls in

  fun_defs @ mem_def :: source,
  fun_decls @ mem_decl :: header

let translate_type_def td =
  C.Def
    (
      match td with
      | Td_user td ->
        C.Df_enum
          {
            C.e_name = td.Ast_misc.ty_name;
            C.e_tags = td.Ast_misc.ty_body;
          }
      | Td_struct (name, fields) ->
        C.Df_struct
          {
            C.s_name = name;
            C.s_fields = List.map translate_var_dec fields;
          }
    )

let translate file =
  let source, header =
    List.fold_left translate_machine ([], []) file.f_machines
  in
  let header =
    let ty_defs = List.map translate_type_def file.f_type_defs in
    {
      C.f_name = file.f_name;
      C.f_kind = C.Header;
      C.f_includes = ["nir"];
      C.f_body = ty_defs @ List.rev header;
    }
  in
  let source =
    {
      C.f_name = file.f_name;
      C.f_kind = C.Source;
      C.f_includes = ["nir"; String.lowercase file.f_name];
      C.f_body = List.rev source;
    }
  in
  [header; source]

(* {2 Generated code} *)

let serialize_file file =
  let fn =
    let ext =
      match file.C.f_kind with
      | C.Source -> ".c"
      | C.Header -> ".h"
    in
    Filename.concat
      (Initial.get_current_file_directory ())
      (String.lowercase file.C.f_name ^ ext)
  in
  let oc = open_out fn in
  let fmt = Format.formatter_of_out_channel oc in
  C_printer.print_file fmt file;
  Format.fprintf fmt "@?";
  close_out oc

let code_for_file file =
  object
    val files = translate file
    method print fmt =
      List.iter (C_printer.print_file fmt) files
    method serialize () =
      List.iter serialize_file files
  end

(* {2 Putting it all together} *)

let file ctx file =
  ctx, code_for_file file

let pass =
  let open Pass_manager in
  P_transform
    (make_transform
       ~ext:"c.tmp"
       ~print_out:Target.print_target_code
       "target_c"
       file)
