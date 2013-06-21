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

open Acids_preclock

(** {2 Errors} *)

type error =
  | Non_causal of Ident.t

exception Eval_error of error

let print_error fmt err =
  match err with
  | Non_causal id ->
    Format.fprintf fmt "Variable %a has been defined in terms of itself"
      Ident.print id

let non_causal id =
  raise (Eval_error (Non_causal id))

(** {2 Values and related functions} *)

type value =
  | Const of Ast_misc.const
  | Tuple of value list

let ill_typed str = invalid_arg (str ^ ": ill-typed")

let get_bool v =
  let open Ast_misc in
  match v with
  | Const (Cconstr (Ec_bool b)) -> b
  | _ -> ill_typed "get_bool"

let get_int v =
  let open Ast_misc in
  match v with
  | Const (Cconstr (Ec_int i)) -> i
  | _ -> ill_typed "get_int"

let get_tuple v =
  match v with
  | Tuple v_l -> v_l
  | _ -> ill_typed "get_tuple"

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    current_nodes : node_def Names.ShortEnv.t;
    current_defs : eq Ident.Env.t;
    idents : value Ident.Env.t;
    computing : Ident.Set.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    current_nodes = Names.ShortEnv.empty;
    current_defs = Ident.Env.empty;
    idents = Ident.Env.empty;
    computing = Ident.Set.empty;
  }

let reset_env env =
  {
    env with
      current_defs = Ident.Env.empty;
      idents = Ident.Env.empty;
      computing = Ident.Set.empty;
  }

let find_value env id =
  Ident.Env.find id env.idents

let add_value env id value =
  assert (not (Ident.Env.mem id env.idents));
  { env with idents = Ident.Env.add id value env.idents; }

let register_as_being_computed env id =
  if Ident.Set.mem id env.computing then non_causal id;
  { env with computing = Ident.Set.add id env.computing; }

let find_equation_for env id =
  Ident.Env.find id env.current_defs

(** {2 Static evaluation itself}

    We walk the AST and replace expressions in pword by their evaluation.
*)

let rec eval_static_clock_exp env ce =
  assert (ce.ce_info#ci_static <> Static_types.S_dynamic);
  match ce.ce_desc with
  | Ce_var v ->
    compute_var env v
  | _ ->
    assert false


and compute_var env id =
  try find_value env id, env
  with Not_found ->
    let env = register_as_being_computed env id in
    let eq = find_equation_for env id in
    let env = enrich_with_eq env eq in
    find_value env id, env

and enrich_with_eq env eq =
  let value, env = eval_static_exp env eq.eq_rhs in
  enrich_with_pat env eq.eq_lhs value

and eval_static_exp env e =
  assert (e.e_info#ei_static
          <> Static_types.Sy_scal Static_types.S_dynamic);
  assert false

and enrich_with_pat env pat value =
  match pat.p_desc with
  | P_var (v, _) -> add_value env v value
  | P_tuple p_l ->
    let v_l = get_tuple value in
    List.fold_left2 enrich_with_pat env p_l v_l
  | P_clock_annot (p, _) | P_type_annot (p, _) -> enrich_with_pat env p value
  | P_split p ->
    let p_l =
      Ast_misc.fold_upword (fun p p_l -> p :: p_l) (fun _ p_l -> p_l) p []
    in
    List.fold_left (fun env p -> enrich_with_pat env p value) env p_l

let eval_file ctx (file : < interfaces : Interface.env > Acids_preclock.file) =
  ctx, file

(** {2 Putting it all together} *)

let eval =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_preclock.print_file
       "static_eval"
       eval_file)
