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
  | Ill_formed_interface of Names.shortname

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
  | Ill_formed_interface intfn ->
    Format.fprintf fmt "the internal interface file for %a is ill-formed"
      Names.print_shortname intfn

let could_not_open_file filen =
  raise (Interface_error (Could_not_open_file filen))

let bad_magic_number filen =
  raise (Interface_error (Bad_magic_number filen))

let could_not_find_file filen =
  raise (Interface_error (Could_not_find_file filen))

let ill_formed_interface intfn =
  raise (Interface_error (Ill_formed_interface intfn))

(** {2 Definitions of data types} *)

type static_node_decl =
  {
    sn_info : Acids_static.Info.node_info;
    sn_body : Acids_static.node_def;
  }

type dynamic_node_decl =
  {
    dn_info : Acids_clocked.Info.node_info;
    dn_body : unit; (* Nir.t option *)
  }

type node_item =
  | I_static of static_node_decl
  | I_dynamic of dynamic_node_decl

type type_item =
  {
    td_constr : Names.shortname list;
  }

type t =
  {
    i_name : Names.shortname;
    (** maps node names to node items *)
    i_nodes : node_item Names.ShortEnv.t;
    (** maps type names to constr list *)
    i_types : type_item Names.ShortEnv.t;
    (** maps constr name to type name *)
    i_constrs : Names.shortname Names.ShortEnv.t;
  }

type env = t Names.ShortEnv.t

(** {2 Access functions} *)

let data_signature_of_node_item ni =
  match ni with
  | I_static snd -> snd.sn_info#ni_data
  | I_dynamic dnd -> dnd.dn_info#ni_data

let static_signature_of_node_item ni =
  match ni with
  | I_static snd -> snd.sn_info#ni_static
  | I_dynamic dnd -> dnd.dn_info#ni_static

let clock_signature_of_node_item ni =
  match ni with
  | I_static _ -> invalid_arg "clock_signature_of_node_item: static node"
  | I_dynamic dnd -> dnd.dn_info#ni_clock

let node_definition_of_node_item ni =
  match ni with
  | I_static snd -> snd.sn_body
  | I_dynamic _ -> invalid_arg "node_definition_of_node_item"

let find_node intf shortn = Names.ShortEnv.find shortn intf.i_nodes

let find_type intf shortn = Names.ShortEnv.find shortn intf.i_types

let find_constructor_rank intf cstr =
  assert false

(** {2 Consistency check and recovery functions} *)

let check_type_and_constrs intf =
  let ill_formed () = ill_formed_interface intf.i_name in

  (* check that each constructor is mapped to the proper type name *)
  let check_constr constr type_name =
    let constrs_for_type_name = Names.ShortEnv.find type_name intf.i_types in
    if not (List.mem constr constrs_for_type_name.td_constr) then ill_formed ()
  in
  Names.ShortEnv.iter check_constr intf.i_constrs;

  (* check that each constructor in each type name exists (no need to re-check
     the constr -> type mapping) *)
  let check_type _ constrs =
    let check_constr constr =
      if not (Names.ShortEnv.mem constr intf.i_constrs)
      then ill_formed ()
    in
    List.iter check_constr constrs.td_constr
  in
  Names.ShortEnv.iter check_type intf.i_types;

  (* check for duplicate constr name *)
  let check_duplicate _ constrs already_seen =
    let check_constr already_seen constr =
      if Utils.String_set.mem constr already_seen
      then ill_formed ()
      else Utils.String_set.add constr already_seen
    in
    List.fold_left check_constr already_seen constrs.td_constr
  in
  ignore
    (Names.ShortEnv.fold check_duplicate intf.i_types Utils.String_set.empty)

let rebuild_constrs_env intf =
  let add type_name constrs constr_env =
    let add constr_env constr =
      Names.ShortEnv.add constr type_name constr_env
    in
    List.fold_left add constr_env constrs.td_constr
  in
  {
    intf with
      i_constrs =
      Names.ShortEnv.fold add intf.i_types Names.ShortEnv.empty;
  }

(** {2 Low-level I/O functions} *)

let load_interface filen =
  try
    let ic = open_in_bin filen in
    let i = input_binary_int ic in
    if i != Compiler.magic_number then bad_magic_number filen;
    let (intf : t) = Marshal.from_channel ic in
    close_in ic;
    Some intf
  with Sys_error _ -> None

let store_interface filen intf =
  try
    let oc = open_out_bin filen in
    output_binary_int oc Compiler.magic_number;
    Marshal.to_channel oc intf [];
    close_out oc
  with _ -> could_not_open_file filen

(** {2 Look-up functions} *)

let module_name_of_file_name filen =
  String.capitalize (Filename.chop_extension (Filename.basename filen))

let interface_file_name_of_module_name modn =
  String.uncapitalize modn ^ ".aso"

let load_interface_from_module_name modn =
  let filen = String.uncapitalize modn ^ ".aso" in
  let rec try_dirs dirs =
    match dirs with
    | [] -> could_not_find_file filen
    | dirn :: dirs ->
      (
        match load_interface (Filename.concat dirn filen) with
        | Some intf -> intf
        | None -> try_dirs dirs
      )
  in
  try_dirs !Compiler_options.search_path
