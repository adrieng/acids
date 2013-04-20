(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013
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

(** {2 Error handling} *)

type error =
  | Could_not_open_file of string
  | Bad_magic_number of string
  | Could_not_find_file of string

exception Interface_error of error

let print_error fmt err =
  match err with
  | Could_not_open_file filen ->
    Format.fprintf fmt "Could not open interface file %s" filen
  | Bad_magic_number filen ->
    Format.fprintf fmt "Bad magic number in file %s" filen
  | Could_not_find_file filen ->
    Format.fprintf fmt "Could not find file %s in @[%a@]"
      filen
      (Utils.print_list_r Utils.print_string ";") !Compiler_options.search_path

let could_not_open_file filen =
  raise (Interface_error (Could_not_open_file filen))

let bad_magic_number filen =
  raise (Interface_error (Bad_magic_number filen))

let could_not_find_file filen =
  raise (Interface_error (Could_not_find_file filen))

(** {2 Definitions of data types} *)

type static_node_decl =
    {
      sn_info : Acids_preclock.Info.node_info;
      sn_body : Acids_preclock.node;
    }

type dynamic_node_decl =
    {
      dn_info : Acids_clocked.Info.node_info;
      dn_body : unit; (* Nir.t option *)
    }

type node_decl =
  | Nd_static of static_node_decl
  | Nd_dynamic of dynamic_node_decl

type t =
    {
      i_name : Names.shortname;
      i_body : node_decl Names.ShortEnv.t;
    }

(** {2 Low-level I/O functions} *)

let load_interface filen =
  try
    let ic = open_in_bin filen in
    let i = input_binary_int ic in
    if i != Compiler.magic_number then bad_magic_number filen;
    let (intf : t) = Marshal.from_channel ic in
    close_in ic;
    intf
  with _ -> could_not_open_file filen

let store_interface filen intf =
  try
    let oc = open_out_bin filen in
    output_binary_int oc Compiler.magic_number;
    Marshal.to_channel oc intf [];
    close_out oc
  with _ -> could_not_open_file filen

(** {2 Look-up functions} *)

let load_interface_from_module_name modn =
  let filen =
    Filename.concat
      (String.uncapitalize modn)
      "aso"
  in
  let rec try_dirs dirs =
    match dirs with
    | [] -> could_not_find_file filen
    | dirn :: dirs ->
      try load_interface (Filename.concat dirn filen)
      with Not_found -> try_dirs dirs
  in
  try_dirs !Compiler_options.search_path
