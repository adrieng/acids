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

open Nir

(** {2 Utilities} *)

let node_invariant invar =
  Pass_manager.prop
    (fun _ file ->
      let check_invar node =
        try invar node
        with Failure reason ->
          failwith (Printf.sprintf "Node %s: %s" node.n_name reason)
      in
      try List.iter check_invar file.f_body; None
      with Failure msg -> Some msg)

(** {2 Scoping} *)

let all_vars_well_def node =
  let vars = Nir_utils.vars_block node.n_body in
  let check v =
    if not (Ident.Env.mem v node.n_env)
    then failwith ("unknown variable " ^ Ident.to_string v)
  in
  List.iter check vars

(** {2 Putting it all together} *)

let all : (unit, Interface.env) Nir.file Pass_manager.prop =
  let invars =
    [
      all_vars_well_def;
    ]
  in
  Pass_manager.(Utils.fold_left_1 both (List.map node_invariant invars))
