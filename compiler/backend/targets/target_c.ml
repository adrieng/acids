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

(*
  Things to document:

  * General structure of the code

  * Calling convention

  * Runtime system
*)

(******************************************************************************)
(* {2 Helpers} *)

let lit_int i = C.Const Ast_misc.(Cconstr (Ec_int i))
let lit_int_e i = C.ConstExp (lit_int i)

let longname ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ln.shortn
  | Module modn -> modn ^ "_" ^ ln.shortn

let mem_struct_name ln = Backend_utils.mem_name (longname ln)
let method_name ln methd = longname ln ^ "_" ^ methd

let op_add = "+"
let op_max = "max"
let op_lt = "<"

let fun_decl_of_fun_def (fdef : C.fdef) =
  let open C in
  {
    d_name = fdef.f_name;
    d_output = fdef.f_output;
    d_input = List.map (fun vd -> vd.v_type) fdef.f_input;
  }

(******************************************************************************)
(* {2 AST walking} *)

let rec translate_ty ty =
  match ty with
  | Ty_scal tys -> C.Scal tys
  | Ty_arr (ty, size) -> C.Array (translate_ty ty, size)
  | Ty_mach mty -> C.Struct (mem_struct_name mty.mt_name)

let rec translate_const cst =
  match cst with
  | C_scal c ->
    C.Const c
  | C_array a ->
    C.Array_lit (List.map translate_const a)
  | C_sizeof ty ->
    C.Sizeof (translate_ty ty)

let translate_var_dec vd =
  {
    C.v_name = vd.v_name;
    C.v_type = translate_ty vd.v_type;
    C.v_init = None;
  }

let translate_methd mach_name methd =
  let mem = Ident.make_internal "mem" in

  let rec translate_lvalue lv =
    match lv with
    | L_var ((K_local | K_input), id) ->
      C.Var id
    | L_var (K_output, id) ->
      C.Deref (C.Var id)
    | L_var (K_field, id) ->
      C.Field (C.Deref (C.Var mem), id)
    | L_arrindex (lv, e) ->
      C.Index (translate_lvalue lv, translate_exp e)

  and translate_exp e =
    match e with
    | E_lval lv ->
      C.Lvalue (translate_lvalue lv)
    | E_const c ->
      C.ConstExp (translate_const c)
  in

  let translate_call call =
    let fun_n = method_name call.c_mach.mt_name call.c_method in

    let inputs = List.map translate_exp call.c_inputs in
    let outputs =
      let outputs = List.map translate_lvalue call.c_outputs in
      List.map (fun lv -> C.AddrOf lv) outputs
    in

    let args = inputs @ outputs in
    let args =
      match call.c_inst with
      | None -> args
      | Some lv -> C.(AddrOf (translate_lvalue lv)) :: args
    in
    let args =
      List.map (fun c -> C.ConstExp (translate_const c)) call.c_mach.mt_cparams
      @ args
    in

    C.Exp (C.Call (fun_n, args))
  in

  let rec translate_stm stm =
    match stm with
    | S_affect (lv, e) ->
      C.Affect (translate_lvalue lv, translate_exp e)
    | S_call call ->
      translate_call call
    | S_loop (vd, stop, bound, body) ->
      let open C in
      let incr =
        (* x = x + 1 *)
        Affect (Var vd.v_name,
                Op (op_add, [Lvalue (Var vd.v_name); lit_int_e Int.one]))
      in

      let stop =
        Op (op_lt, [Lvalue (Var vd.v_name);
                    Op(op_max, [translate_exp stop; lit_int_e bound])])
      in

      For
        (
          translate_var_dec vd,
          lit_int_e Int.zero,
          stop,
          incr,
          translate_stm body
        )
    | S_switch (e, cases) ->
      C.Switch
        (
          translate_exp e,
          List.map (fun (ec, stm) -> ec, translate_stm stm) cases
        )
    | S_block block ->
      C.Block (translate_block block)

  and translate_block block =
    {
      C.b_locals = List.map translate_var_dec block.b_locals;
      C.b_body = List.map translate_stm block.b_body;
    }
  in

  let mem_input =
    let open C in
    {
      v_name = mem;
      v_type = Pointer (Struct (mem_struct_name mach_name));
      v_init = None;
    }
  in

  let inputs =
    let add_deref vd = C.({ vd with v_type = Pointer vd.v_type; }) in
    List.map translate_var_dec methd.m_inputs
    @ List.map (fun vd -> add_deref (translate_var_dec vd)) methd.m_outputs
  in

  {
    C.f_name = method_name mach_name methd.m_name;
    C.f_output = None;
    C.f_input = mem_input :: inputs;
    C.f_body = translate_block methd.m_body;
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

  let fun_defs = List.rev_map (translate_methd mach.ma_name) mach.ma_methods in
  let fun_decls = List.map fun_decl_of_fun_def fun_defs in
  let fun_defs = List.map (fun f -> C.(Def (Df_function f))) fun_defs in
  let fun_decls = List.map (fun f -> C.(Decl (Dc_function f))) fun_decls in

  fun_defs @ mem_def :: source,
  fun_decls @ mem_decl :: header

let translate_type_def td =
  C.Def
    (
      C.Df_enum
        {
          C.e_name = td.Ast_misc.ty_name;
          C.e_tags = td.Ast_misc.ty_body;
        }
    )

let translate file =
  let source, header =
    List.fold_left translate_machine ([], []) file.f_machines
  in
  let header =
    let enums = List.map translate_type_def file.f_type_defs in
    {
      C.f_name = file.f_name;
      C.f_kind = C.Header;
      C.f_includes = ["nir"];
      C.f_body = enums @ List.rev header;
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
