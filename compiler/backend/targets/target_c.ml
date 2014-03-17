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

let name = "c"

type t = C.file list

let print fmt file =
  List.iter (C_printer.print_file fmt) file

(* {2 Environments} *)

type pword_info =
  {
    pword : Ast_misc.const_pword;
    prefix_size : Int.t;
    data_ident : Ident.t;
    length_ident : Ident.t;
  }

type env =
  {
    pwords : pword_info Ident.Env.t;
  }

let initial_env _ =
  {
    pwords = Ident.Env.empty;
  }

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

(* {2 Helpers} *)

let longname ln =
  let open Names in
  let modn =
    match ln.modn with
    | LocalModule ->
      Interface.get_current_module_name ()
    | Module modn ->
      modn
  in
  modn ^ "_" ^ ln.shortn

let ident id =
  Ident.to_string id

(******************************************************************************)

let mem s = s ^ "_mem"
let reset s = s ^ "_reset"
let step s = s ^ "_step"

let mem_name ln = mem (longname ln)
let reset_name ln = reset (longname ln)
let step_name ln = step (longname ln)

let pword = "pword"
let pword_mem = mem pword
let pword_reset = reset pword
let pword_step = step pword

(******************************************************************************)

(* {2 AST walking} *)

let translate_pword env defs x_p pw =
  let x_p_dat = Ident.make_suffix x_p "_dat" in
  let x_p_len = Ident.make_suffix x_p "_len" in

  let prefix_size, p = Tree_word.pair_list_of_pword_int pw in
  let p_dat, p_len = List.split p in

  let make_static id mk body =
    C.Def
      (
        C.Df_static
          (
            { C.v_name = ident id; C.v_type = C.Pointer C.Int; },
          let mk x = C.Const (Ast_misc.Cconstr (mk x)) in
          C.Array_lit (List.map mk body)
          )
      )
  in

  let p_dat = make_static x_p_dat (fun x -> x) p_dat in
  let p_len = make_static x_p_len (fun x -> Ast_misc.Ec_int x) p_len in

  add_pword env x_p pw prefix_size ~data:x_p_dat ~length:x_p_len,
  p_dat :: p_len :: defs

let translate_buff_dec bd =
  {
    C.v_name = ident bd.b_name;
    C.v_type = C.Name "buffer";
  }

let translate_inst (env, defs) inst =
  let env, defs, ty =
    match inst.i_kind with
    | Mach ln ->
      env, defs, C.Name (mem_name ln)
    | Pword pw ->
      let env, defs = translate_pword env defs inst.i_name pw in
      env, defs, C.Name pword_mem
  in
  (env, defs),
  {
    C.v_name = ident inst.i_name;
    C.v_type = ty;
  }

let make_step_function env mach =
  let mem = ident (Ident.make_internal "mem") in

  {
    C.f_name = step_name mach.m_name;
    C.f_output = None;
    C.f_input =
      [
        {
          C.v_name = mem;
          C.v_type = C.Pointer (C.Struct (mem_name mach.m_name));
        }
      ];
    C.f_body =
      {
        C.b_locals = [];
        C.b_body = [];
      }
  }

let make_reset_function mach =
  let reset = reset_name mach.m_name in
  let mem_n = mem_name mach.m_name in
  let mem = ident (Ident.make_internal "mem") in

  let reset_inst inst =
    let call =
      match inst.i_kind with
      | Mach ln ->
        reset_name ln
      | Pword _ ->
        pword_reset
    in

    C.Exp
      (
        C.Call
          (
            call,
            [
              C.AddrOf (C.Field (mem, ident inst.i_name));
            ]
          )
      )
  in
  let body = List.map reset_inst mach.m_insts in

  {
    C.f_name = reset;
    C.f_output = None;
    C.f_input =
      [
        {
          C.v_name = mem;
          C.v_type = C.Pointer (C.Struct mem_n);
        }
      ];
    C.f_body =
      {
        C.b_locals = [];
        C.b_body = body;
      }
  }

let translate_machine (source, header) mach =
  Ident.set_current_ctx mach.m_ctx;
  let env = initial_env mach in

  (* Create internal memory with buffers, nodes and pword instantiations *)
  let mem_name = mem_name mach.m_name in
  let (env, defs), fields =
    Utils.mapfold_left translate_inst (env, []) mach.m_insts
  in
  let mem =
    {
      C.s_name = mem_name;
      C.s_fields =
        List.map translate_buff_dec mach.m_mem
      @ fields;
    }
  in

  (* Create reset function *)
  let reset_def = make_reset_function mach in
  let reset_decl = C_utils.fun_decl_of_fun_def reset_def in

  (* Create step function *)
  let step_def = make_step_function env mach in
  let step_decl = C_utils.fun_decl_of_fun_def step_def in

  let source =
    C.Def (C.Df_function step_def)
    :: C.Def (C.Df_function reset_def)
    :: C.Def (C.Df_struct mem)
    :: defs
    @ source
  in
  let header =
    C.Decl (C.Dc_function step_decl)
    :: C.Decl (C.Dc_function reset_decl)
    :: C.Decl (C.Dc_struct mem_name)
    :: header
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
