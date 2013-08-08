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

open Acids_causal

let print_dynamic_signatures fmt (nn, info) =
  Format.fprintf fmt
    "@[<v 2>val %a@ @[%s %a@]@ @[%s %a@]@ @[%s %a@]@]@\n"
    Names.print_shortname nn
    Data_types.printing_prefix
    Data_types.print_sig info#ni_data
    Static_types.printing_prefix
    Static_types.print_sig info#ni_static
    Clock_types.printing_prefix
    Clock_types.print_sig info#ni_clock

let print_static_signatures fmt nd =
  let open Acids_static in
  Format.fprintf fmt
    "@[<v 2>static val %a@ @[%s %a@]@ @[%s %a@]@]@\n"
    Names.print_shortname nd.n_name
    Data_types.printing_prefix
    Data_types.print_sig nd.n_info#ni_data
    Static_types.printing_prefix
    Static_types.print_sig nd.n_info#ni_static

let print_signatures_of_node_defs file =
  let info_l =
    let add_sig phr info_l =
      match phr with
      | Phr_node_def nd -> (nd.n_name, nd.n_info) :: info_l
      | Phr_node_decl _ | Phr_type_def _ -> info_l
    in
    List.fold_right add_sig file.f_body []
  in
  Format.printf "%a" (Utils.print_list_eol print_dynamic_signatures) info_l;
  if List.length file.f_info#static_nodes > 0 then Format.printf "@\n";
  Format.printf "%a@?"
    (Utils.print_list_eol print_static_signatures) file.f_info#static_nodes
  ;
  flush stdout

let file
    ctx
    (file :
     < interfaces : Interface.env;
       static_nodes : Acids_static.node_def list; > file)
    =
  if Pass_manager.ctx_get_attr ctx "i" then print_signatures_of_node_defs file;
  let intf = Interface.interface_of_file file in
  let fn = Interface.interface_file_name_of_module_name file.f_name in
  let fn = Filename.concat (Pass_manager.ctx_current_dir ctx) fn in
  Interface.store_interface fn intf;
  ctx, file

let save =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:(fun _ _ -> ())
       "save"
       file)
