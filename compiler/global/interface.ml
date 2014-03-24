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
    Format.fprintf fmt "Could not find a valid %s file in [@[%a@]]"
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

type const_node_decl =
  {
    sn_info : Acids_const.Info.node_info;
    sn_body : Acids_const.node_def;
  }

type nonconst_node_decl =
  {
    dn_info : Acids_causal.Info.node_info;
    dn_body : unit; (* Nir.t option *)
  }

type node_item =
  | I_const of const_node_decl
  | I_nonconst of nonconst_node_decl

type type_item =
  {
    td_constr : Names.shortname list;
  }

type const_item =
  {
    si_name : Names.shortname;
    si_type : Data_types.data_ty;
    si_value : Ast_misc.const;
  }

type pword_item =
  {
    pi_name : Names.shortname;
    pi_type : Data_types.data_ty_scal;
    pi_value : Ast_misc.econstr_pword;
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
    (** maps constant name to econstr *)
    i_consts : const_item Names.ShortEnv.t;
    (** maps pword names to pwords *)
    i_pwords : pword_item Names.ShortEnv.t;
  }

type env = t Names.ShortEnv.t

(** {2 Access functions} *)

let data_signature_of_node_item ni =
  match ni with
  | I_const snd -> snd.sn_info#ni_data
  | I_nonconst dnd -> dnd.dn_info#ni_data

let const_signature_of_node_item ni =
  match ni with
  | I_const snd -> snd.sn_info#ni_const
  | I_nonconst dnd -> dnd.dn_info#ni_const

let clock_signature_of_node_item ni =
  match ni with
  | I_const _ -> invalid_arg "clock_signature_of_node_item: const node"
  | I_nonconst dnd -> dnd.dn_info#ni_clock

let node_definition_of_node_item ni =
  match ni with
  | I_const snd -> snd.sn_body
  | I_nonconst _ -> invalid_arg "node_definition_of_node_item"

let find_node intf shortn = Names.ShortEnv.find shortn intf.i_nodes

let find_type intf shortn = Names.ShortEnv.find shortn intf.i_types

let find_constructor intf shortn = Names.ShortEnv.find shortn intf.i_constrs

let find_constructors_of_type intf shortn =
  let td = Names.ShortEnv.find shortn intf.i_types in
  td.td_constr

let find_constructor_rank intf cstr =
  let ty_n = find_constructor intf cstr in
  let ty_i = find_type intf ty_n in
  Utils.find_rank cstr ty_i.td_constr

let find_const intf shortn = Names.ShortEnv.find shortn intf.i_consts

let find_pword intf shortn = Names.ShortEnv.find shortn intf.i_pwords

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
  with Sys_error _ | Failure _ -> None

let store_interface filen intf =
  try
    let oc = open_out_bin filen in
    output_binary_int oc Compiler.magic_number;
    Marshal.(to_channel oc intf [Closures]);
    close_out oc
  with _ -> could_not_open_file filen

(** {2 Look-up functions} *)

let module_name_of_file_name filen =
  String.capitalize (Filename.chop_extension (Filename.basename filen))

let interface_file_name_of_module_name modn =
  String.uncapitalize modn ^ ".aso"

let get_current_module_name () =
  module_name_of_file_name (Initial.get_current_file_name ())

let qualify_shortname shortn =
  let fn = Initial.get_current_file_name () in
  let modn = module_name_of_file_name fn in
  Initial.make_longname ~modn shortn

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

(** {2 High-level functions} *)

let interface_of_file file =
  let open Acids_causal in

  let add_nonconst node_env phr =
    match phr with
    | Phr_node_def nd ->
      Names.ShortEnv.add
        nd.n_name
        (
          I_nonconst
            {
              dn_info = nd.n_info;
              dn_body = ();
            }
        )
        node_env
    | Phr_node_decl nd ->
      let n_info =
        object
          method ni_ctx = Ident.make_ctx ()
          method ni_data = nd.decl_data
          method ni_const = nd.decl_const
          method ni_clock = nd.decl_clock
        end
      in
      Names.ShortEnv.add
        nd.decl_name
        (
          I_nonconst
            {
              dn_info = n_info;
              dn_body = ();
            }
        )
        node_env
    | Phr_type_def _ | Phr_const_def _ | Phr_pword_def _ ->
      node_env
  in

  let add_const node_env nd =
    let open Acids_const in
    Names.ShortEnv.add
      nd.n_name
      (I_const { sn_info = nd.n_info; sn_body = nd; })
      node_env
  in

  let node_env = Names.ShortEnv.empty in
  let node_env = List.fold_left add_nonconst node_env file.f_body in
  let node_env = List.fold_left add_const node_env file.f_info#const_nodes in

  let add_type (type_env, constr_env) phr =
    match phr with
    | Phr_node_def _ | Phr_node_decl _ | Phr_const_def _ | Phr_pword_def _ ->
      type_env, constr_env
    | Phr_type_def td ->
      let open Ast_misc in
      let constr_env =
        let add_constr constr_env c =
          Names.ShortEnv.add c td.ty_name constr_env
        in
        List.fold_left add_constr constr_env td.ty_body
      in
      let type_env =
        Names.ShortEnv.add td.ty_name { td_constr = td.ty_body; } type_env
      in
      type_env, constr_env
  in

  let type_env, constr_env = Names.ShortEnv.empty, Names.ShortEnv.empty in
  let type_env, constr_env =
    List.fold_left add_type (type_env, constr_env) file.f_body
  in

  let add_const const_env phr =
    match phr with
    | Phr_node_def _ | Phr_node_decl _ | Phr_type_def _ | Phr_pword_def _ ->
      const_env
    | Phr_const_def sd ->
      let open Acids_causal in
      let c =
        match sd.sd_body.e_desc with
        | E_const c -> c
        | _ -> assert false (* should be const simplified *)
      in
      let si =
        {
          si_name = sd.sd_name;
          si_type = sd.sd_body.e_info#ei_data;
          si_value = c;
        }
      in
      Names.ShortEnv.add sd.sd_name si const_env
  in
  let const_env = List.fold_left add_const Names.ShortEnv.empty file.f_body in

  let add_pword pword_env phr =
    match phr with
    | Phr_node_def _ | Phr_node_decl _ | Phr_type_def _ | Phr_const_def _ ->
      pword_env
    | Phr_pword_def pd ->
      let open Acids_causal in
      let p =
        Tree_word.map_upword
          (fun se -> se.se_desc)
          (fun se -> Ast_misc.get_int se.se_desc)
          pd.pd_body
      in
      let ty =
        let se = Tree_word.get_first_leaf_period pd.pd_body in
        se.se_info#pwi_data
      in
      let pi =
        {
          pi_name = pd.pd_name;
          pi_type = ty;
          pi_value = p;
        }
      in
      Names.ShortEnv.add pd.pd_name pi pword_env
  in
  let pword_env = List.fold_left add_pword Names.ShortEnv.empty file.f_body in
  {
    i_name = file.f_name;
    i_nodes = node_env;
    i_types = type_env;
    i_constrs = constr_env;
    i_consts = const_env;
    i_pwords = pword_env;
  }
