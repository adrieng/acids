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

let mem_name ln = longname ln ^ "_mem"

let pword = "pword"

(* {2 AST walking} *)

let translate_buff_dec bd =
  {
    C.v_name = ident bd.b_name;
    C.v_type = C.Name "buffer";
  }

let translate_inst_kind kind =
  match kind with
  | Mach ln -> C.Name (mem_name ln)
  | Pword _ -> C.Name pword

let translate_inst inst =
  {
    C.v_name = ident inst.i_name;
    C.v_type = translate_inst_kind inst.i_kind;
  }

let translate_machine (source, header) mach =
  let mem_name = mem_name mach.m_name in
  let mem =
    {
      C.s_name = mem_name;
      C.s_fields =
        List.map translate_buff_dec mach.m_mem
      @ List.map translate_inst mach.m_insts;
    }
  in
  C.Def (C.Df_struct mem) :: source, C.Decl (C.Dc_struct mem_name) :: header

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
