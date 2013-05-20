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

open Acids_typed
open Interval_types

(** {1 Interval typing}

    Nothing special for now. *)

(** {2 Errors} *)

type error =
  | Non_exhaustive_pattern of Loc.t * Ast_misc.econstr

exception Typing_error of error

let print_error fmt err =
  match err with
  | Non_exhaustive_pattern (l, ec) ->
    Format.fprintf fmt "%aThis pattern-matching is not exhaustive@\n"
      Loc.print l;
    Format.fprintf fmt "Here is an example of a value that is not matched:@\n%a"
      Ast_misc.print_econstr ec

let non_exhaustive_pattern loc ec =
  raise (Typing_error (Non_exhaustive_pattern (loc, ec)))

(** {2 High-level utilities} *)

let ty_top = It_scal Is_top

let ty_inter it = It_scal (Is_inter it)

let union_scal ty1 ty2 =
  match ty1, ty2 with
  | Is_top, _ | _, Is_top -> Is_top
  | Is_inter i1, Is_inter i2 -> Is_inter (Interval.join i1 i2)

let rec union ty1 ty2 =
  match ty1, ty2 with
  | It_scal ty1, It_scal ty2 -> It_scal (union_scal ty1 ty2)
  | It_prod ty_l1, It_prod ty_l2 -> It_prod (List.map2 union ty_l1 ty_l2)
  | _ -> assert false (* TODO proper error message *)

(** {2 Typing environments} *)

type typing_env =
  {
    intf_env : Interface.t Names.ShortEnv.t;
    current_types : Names.shortname list Names.ShortEnv.t;
    current_nodes : ty_sig Names.ShortEnv.t;
    idents : ty Ident.Env.t;
  }

let find_ident env v = Ident.Env.find v env.idents

let add_ident env v ty = { env with idents = Ident.Env.add v ty env.idents; }

(** {2 Typing AST nodes} *)

(** The algorithm proceeds in one pass: all variables have to be explicitely
    tagged with their intervals if the user wishes to. *)

let rec type_pat p env =
  let p, ty, env =
    match p.p_desc with
    | P_var (v, info) ->
      let ty =
        match info with
        | None -> ty_top
        | Some it -> ty_inter it
      in
      Acids_interval.P_var (v, info), ty, add_ident env v ty

    | P_tuple p_l ->
      let p_l, env = Utils.mapfold type_pat p_l env in
      let ty_l = List.map (fun p -> p.Acids_interval.p_info#pi_interv) p_l in
      Acids_interval.P_tuple p_l, It_prod ty_l, env

    | _ ->
      assert false
  in
  assert false

let type_file
    ctx
    (file : < interfaces : Interface.t Names.ShortEnv.t > Acids_typed.file) =
  (assert false
     :
     Pass_manager.ctx
     * < interfaces : Interface.t Names.ShortEnv.t > Acids_interval.file)

(** {2 Putting it all together} *)

let type_ =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_interval.print_file
       "intervals"
       type_file)


