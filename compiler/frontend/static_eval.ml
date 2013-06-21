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

let equal_val v1 v2 = v1 = v2

let ill_typed str = invalid_arg (str ^ ": ill-typed")

let const c = Const c

let econstr ec = const (Ast_misc.Cconstr ec)

let bool b = econstr (Ast_misc.Ec_bool b)

let int i = econstr (Ast_misc.Ec_int i)

let tuple v_l = Tuple v_l

let get_econstr v =
  match v with
  | Const (Ast_misc.Cconstr ec) -> ec
  | _ -> ill_typed "get_econstr"

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

let val_fst v =
  match v with
  | Tuple [v; _] -> v
  | _ -> ill_typed "value_fst"

let val_snd v =
  match v with
  | Tuple [_; v] -> v
  | _ -> ill_typed "value_fst"

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

let find_node env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ShortEnv.find ln.shortn env.current_nodes
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    let ni = Interface.find_node intf ln.shortn in
    Interface.node_definition_of_node_item ni

let find_value env id =
  Ident.Env.find id env.idents

let add_value env id value =
  assert (not (Ident.Env.mem id env.idents));
  { env with idents = Ident.Env.add id value env.idents; }

let register_as_being_computed env id =
  if Ident.Set.mem id env.computing then non_causal id;
  { env with computing = Ident.Set.add id env.computing; }

let add_equation env id eq =
  { env with current_defs = Ident.Env.add id eq env.current_defs; }

let find_equation_for env id =
  Ident.Env.find id env.current_defs

(** {2 From expressions to environments} *)

let rec create_env_exp env e =
  match e.e_desc with
  | E_var _ | E_const _ | E_valof _ -> env
  | E_fst e | E_snd e
  | E_app (_, e)
  | E_when (e, _) | E_split (_, e, _)
  | E_clock_annot (e, _) | E_type_annot (e, _)
  | E_dom (e, _) | E_buffer e ->
    create_env_exp env e

  | E_fby (e1, e2) | E_bmerge (_, e1, e2) ->
    let env = create_env_exp env e1 in
    create_env_exp env e2

  | E_ifthenelse (e1, e2, e3) ->
    let env = create_env_exp env e1 in
    let env = create_env_exp env e2 in
    create_env_exp env e3

  | E_tuple e_l ->
    List.fold_left create_env_exp env e_l

  | E_merge (_, c_l) ->
    List.fold_left (fun env c -> create_env_exp env c.c_body) env c_l

  | E_where (e, block) ->
    create_env_exp (create_env_block env block) e

and create_env_block env block =
  let add_eq env eq =
    let rec add_to_relevant_vars env p =
      match p.p_desc with
      | P_var (v, _) -> add_equation env v eq
      | P_tuple p_l -> List.fold_left add_to_relevant_vars env p_l
      | P_clock_annot (p, _) | P_type_annot (p, _) -> add_to_relevant_vars env p
      | P_split p ->
        Ast_misc.fold_upword
          (Utils.flip add_to_relevant_vars)
          (fun _ env -> env)
          p
          env
    in
    add_to_relevant_vars env eq.eq_lhs
  in
  let env = List.fold_left add_eq env block.b_body in
  List.fold_left (fun env eq -> create_env_exp env eq.eq_rhs) env block.b_body

let rec enrich_with_pat env pat value =
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

(** {2 Static evaluation itself}

    We walk the AST and replace expressions in pword by their evaluation.
*)

let not_static s =
  invalid_arg (s ^ ": expression cannot be evaluated")

let rec eval_static_clock_exp ce env =
  assert (ce.ce_info#ci_static <> Static_types.S_dynamic);
  match ce.ce_desc with
  | Ce_var v ->
    compute_var env v
  | Ce_pword w ->
    let rec find_any pt =
      match pt with
      | Ast_misc.Leaf x -> x
      | Ast_misc.Power (pt, _) -> find_any pt
      | Ast_misc.Concat [] -> assert false
      | Ast_misc.Concat (x :: _) -> find_any x
    in
    eval_static_pword_exp (find_any w.Ast_misc.u) env
  | Ce_equal (ce, e) ->
    let val_ce, env = eval_static_clock_exp ce env in
    let val_e, env = eval_static_exp e env in
    bool (equal_val val_ce val_e), env
  | Ce_iter _ ->
    not_static "eval_static_clock_exp"

and compute_var env id =
  try find_value env id, env
  with Not_found ->
    let env = register_as_being_computed env id in
    let eq = find_equation_for env id in
    let value, env = eval_static_exp eq.eq_rhs env in
    let env = enrich_with_pat env eq.eq_lhs value in
    find_value env id, env

and eval_static_exp e env =
  assert (e.e_info#ei_static
          <> Static_types.Sy_scal Static_types.S_dynamic);
  match e.e_desc with
  | E_var v ->
    compute_var env v

  | E_const c ->
    const c, env

  | E_fst e ->
    let value, env = eval_static_exp e env in
    val_fst value, env

  | E_snd e ->
    let value, env = eval_static_exp e env in
    val_snd value, env

  | E_tuple e_l ->
    let v_l, env = Utils.mapfold eval_static_exp e_l env in
    tuple v_l, env

  | E_fby _ ->
    not_static "eval_static_exp"

  | E_ifthenelse (e1, e2, e3) ->
    let v, env = eval_static_exp e1 env in
    eval_static_exp (if get_bool v then e2 else e3) env

  | E_app (app, e) ->
    let v, env = eval_static_exp e env in
    let nd = find_node env app.a_op in
    apply_node env nd v, env

  | E_where (e, _) ->
    eval_static_exp e env

  | E_bmerge (ce, e1, e2) ->
    let v, env = eval_static_clock_exp ce env in
    eval_static_exp (if get_bool v then e1 else e2) env

  | E_merge (ce, c_l) ->
    let v, env = eval_static_clock_exp ce env in
    let ec = get_econstr v in
    let c = List.find (fun c -> c.c_sel = ec) c_l in
    eval_static_exp c.c_body env

  | E_valof ce ->
    eval_static_clock_exp ce env

  | E_when (e, _) | E_split (_, e, _)
  | E_clock_annot (e, _) | E_type_annot (e, _)
  | E_dom (e, _) | E_buffer e ->
    eval_static_exp e env

and eval_static_pword_exp pwe env =
  assert (pwe.pwe_info#pwi_static <> Static_types.S_dynamic);
  match pwe.pwe_desc with
  | Pwe_var v ->
    compute_var env v
  | Pwe_econstr ec ->
    econstr ec, env
  | Pwe_fword ec_l ->
    int (List.hd ec_l), env

and apply_node env nd value =
  let env = reset_env env in
  let env = enrich_with_pat env nd.n_input value in
  assert false

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
