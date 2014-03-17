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

  push(&buffer_state, buffer_capacity, amount, data)

  vs.

  pop(&buffer_state, buffer_capacity, amount, result)
*)

let name = "c"

type t = C.file list

let print fmt file =
  List.iter (C_printer.print_file fmt) file

let ident id =
  Ident.to_string id

(* {2 Environments} *)

type pword_info =
  {
    pword : Ast_misc.const_pword;
    prefix_size : Int.t;
    data_ident : Ident.t;
    length_ident : Ident.t;
  }

type buffer_info =
  {
    local : bool;
    capacity : Int.t;
    ty : C.ty;
  }

type env =
  {
    mem : Ident.t;
    pwords : pword_info Ident.Env.t;
    buffers : buffer_info Ident.Env.t;
  }

let initial_env _ =
  {
    mem = Ident.make_internal "";
    pwords = Ident.Env.empty;
    buffers = Ident.Env.empty;
  }

let set_mem env mem = { env with mem = mem; }

let add_pword env id pw pref ~data ~length =
  let pi =
    {
      pword = pw;
      prefix_size = pref;
      data_ident = data;
      length_ident = length;
    }
  in
  { env with pwords = Ident.Env.add id pi env.pwords; }

let find_pword env id =
  Ident.Env.find id env.pwords

let add_buffer env id local capacity ty =
  let info =
    {
      local = local;
      capacity = capacity;
      ty = ty;
    }
  in
  { env with buffers = Ident.Env.add id info env.buffers; }

let find_buffer env id =
  let info = Ident.Env.find id env.buffers in
  C.(if info.local then Var id else Field (env.mem, id)),
  info.capacity,
  info.ty

(******************************************************************************)
(* {2 Helpers} *)

let mem s = s ^ "_mem"
let reset s = s ^ "_reset"
let step s = s ^ "_step"

let mem_name ln = mem (longname ln)
let reset_name ln = reset (longname ln)
let step_name ln = step (longname ln)

let pword = "nir_pword"
let pword_mem = mem pword
let pword_reset = reset pword
let pword_step = step pword

let buffer = "nir_buffer"
let buffer_mem = mem buffer
let buffer_reset = reset buffer
let buffer_step = step buffer

let method_name ln kind =
  let suff =
    match kind with
    | Step -> "_step"
    | Reset -> "_reset"
  in
  longname ln ^ suff

let boxed = "nir_boxed"
let push = "nir_push"
let pop = "nir_pop"

(******************************************************************************)

(* {2 AST walking} *)

let translate_pword env locals x_p pw =
  let x_p_dat = Ident.make_suffix x_p "_dat" in
  let x_p_len = Ident.make_suffix x_p "_len" in

  let prefix_size, p = Tree_word.pair_list_of_pword_int pw in
  let p_dat, p_len = List.split p in

  let make_static id mk body =
    {
      C.v_name = id;
      C.v_type = C.Pointer int_ty;
      C.v_init =
        let mk x = C.Const (Ast_misc.Cconstr (mk x)) in
        Some (C.Array_lit (List.map mk body));
    }
  in

  let p_dat = make_static x_p_dat (fun x -> x) p_dat in
  let p_len = make_static x_p_len (fun x -> Ast_misc.Ec_int x) p_len in

  add_pword env x_p pw prefix_size ~data:x_p_dat ~length:x_p_len,
  p_dat :: p_len :: locals

let rec translate_ty_local ty =
  match ty with
  | Ty_scal tys -> C.Scal tys
  | Ty_arr (ty, size) -> C.Array (translate_ty_local ty, size)
  | Ty_boxed -> C.Name boxed

let rec translate_ty_input ty =
  match ty with
  | Ty_scal tys -> C.Scal tys
  | Ty_arr (ty, _) -> C.Pointer (translate_ty_input ty)
  | Ty_boxed -> C.Name boxed

let rec translate_ty_output ty =
  match ty with
  | Ty_scal tys -> C.Pointer (C.Scal tys)
  | Ty_arr (ty, _) -> translate_ty_output ty
  | Ty_boxed -> C.Name boxed

let translate_inst local (env, defs) inst =
  let env, defs, ty =
    match inst.i_kind with
    | Mach ln ->
      env, defs, C.Name (mem_name ln)
    | Pword pw ->
      let env, defs = translate_pword env defs inst.i_name pw in
      env, defs, C.Name pword_mem
    | Buffer (ty, capacity) ->
      let ty = translate_ty_local ty in
      let env = add_buffer env inst.i_name local capacity ty in
      env, defs, C.Name buffer_mem
  in
  (env, defs),
  {
    C.v_name = inst.i_name;
    C.v_type = ty;
    C.v_init = None;
  }

let translate_var_dec ?(translate_ty = translate_ty_local) vd =
  {
    C.v_name = vd.v_name;
    C.v_type = translate_ty vd.v_type;
    C.v_init = None;
  }

let rec translate_lvalue lv =
  match lv with
  | Var v ->
    C.Var v
  | Index (id, e) ->
    C.Index (id, translate_exp e)

and translate_exp e =
  match e with
  | Const c ->
    C.(ConstExp (Const c))
  | Lvalue lv ->
    C.Lvalue (translate_lvalue lv)

let translate_op op =
  match op with
  | "(+)" | "(-)" | "(*)" | "(/)"
  | "(<)" | "(<=)" | "(>)" | "(>=)" ->
    Some (String.sub op 1 (String.length op - 2))
  | "(+.)" | "(-.)" | "(*.)" | "(/.)" ->
    Some (String.sub op 1 1)
  | "(=)" ->
    Some "=="
  | _ ->
    None

let is_op op = translate_op op <> None

let rec translate_stm env acc stm =
  match stm with
  | Skip ->
    acc

  | Call { c_kind = Builtin op; c_inputs = x_l; c_outputs = y_l; } ->
    (
      let open C in
      match translate_op op with
      | Some op ->
        let y = Utils.assert1 y_l in
        Affect
          (
            translate_lvalue y,
            Op (op, List.map translate_exp x_l)
          )
        :: acc
      | None ->
        Exp
          (
            Call
              (
                op,
                List.map translate_exp x_l
                @ List.map (fun lv -> AddrOf (translate_lvalue lv)) y_l
              )
          )
          :: acc
    )

  | Call _ ->
    acc

  | Affect (lv, e) ->
    C.Affect (translate_lvalue lv, translate_exp e) :: acc

  | Box _ ->
    acc
  | Unbox _ ->
    acc

  | Push (b, amount, x) ->
    let open C in
    let lv, capacity, ty = find_buffer env b in
    Exp
      (Call
         (
           push,
           [
             AddrOf lv;
             C_utils.int capacity;
             Op ("*", [translate_exp amount; Sizeof ty]);
             Lvalue (Var x);
           ]
         )
      )
    ::
    acc

  | Pop (b, amount, x) ->
    let open C in
    let lv, capacity, ty = find_buffer env b in
    Exp
      (Call
         (
           pop,
           [
             AddrOf lv;
             C_utils.int capacity;
             Op ("*", [translate_exp amount; Sizeof ty]);
             AddrOf (Var x);
           ]
         )
      )
    ::
    acc

  | Reset _ ->
    acc

  | Switch _ ->
    acc

  | For _ ->
    acc

  | Block block ->
    C.Block (translate_block env block) :: acc

and translate_block env block =
  let locals = List.map translate_var_dec block.b_vars in
  let (env, local_pwords), locals =
    Utils.mapfold_left (translate_inst true) (env, locals) block.b_insts
  in
  let body = List.fold_left (translate_stm env) [] block.b_body in
  {
    C.b_locals = locals @ local_pwords;
    C.b_body = List.rev body;
  }

let translate_method env mach_name methd =
  let mem = Ident.make_internal "mem" in
  let env = set_mem env mem in
  let inputs =
    List.map
      (translate_var_dec ~translate_ty:translate_ty_input)
      methd.m_inputs
  in
  let outputs =
    List.map
      (translate_var_dec ~translate_ty:translate_ty_output)
      methd.m_outputs
  in
  {
    C.f_name = method_name mach_name methd.m_kind;
    C.f_output = None;
    C.f_input =
      {
        C.v_name = mem;
        C.v_type = C.Pointer (C.Struct (mem_name mach_name));
        C.v_init = None;
      }
    :: inputs @ outputs;
    C.f_body = translate_block env methd.m_body;
  }

let translate_machine (source, header) mach =
  Ident.set_current_ctx mach.m_ctx;
  let env = initial_env mach in

  (* Create internal memory with buffers, nodes and pword instantiations *)
  let mem_name = mem_name mach.m_name in
  let (env, pword_vars), fields =
    Utils.mapfold_left (translate_inst false) (env, []) mach.m_insts
  in
  let mem =
    {
      C.s_name = mem_name;
      C.s_fields = fields;
    }
  in

  let fun_defs = List.map (translate_method env mach.m_name) mach.m_methods in
  let fun_decls = List.map fun_decl_of_fun_def fun_defs in

  let source =
    List.rev_map (fun d -> C.(Def (Df_function d))) fun_defs
    @ [C.Def (C.Df_struct mem)]
    @ List.map (fun d -> C.(Def (Df_static d))) pword_vars
    @ source
  in
  let header =
    List.rev_map (fun d -> C.(Decl (Dc_function d))) fun_decls
    @ [C.Decl (C.Dc_struct mem_name)]
    @ header
  in
  source, header

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
      C.f_body =
        enums @ List.rev header;
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

(* {2 Serialization} *)

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

let serialize out =
  List.iter serialize_file out
