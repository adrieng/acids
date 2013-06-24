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

open Acids_static

(** {2 Exceptions} *)

type error =
  | Non_causal of Loc.t * Names.shortname * Ident.t

exception Simplification_error of error

let print_error fmt err =
  match err with
  | Non_causal (l, nn, v) ->
    Format.fprintf fmt "%aStatic variable %a in node %a is defined in terms of itself"
      Loc.print l
      Ident.print v
      Names.print_shortname nn

let non_causal loc nn v =
  raise (Simplification_error (Non_causal (loc, nn, v)))

(** {2 Utility functions} *)

let get_econstr value =
  let open Static_eval in
  let open Ast_misc in
  match value with
  | Const (Cconstr ec) -> ec
  | _ -> invalid_arg "get_econstr"

let get_int value =
  let open Static_eval in
  let open Ast_misc in
  match value with
  | Const (Cconstr (Ec_int i)) -> i
  | _ -> invalid_arg "get_int"

(** {2 Environments} *)

type env =
  {
    eval_env : Static_eval.env;
    static_nodes : Acids_static.node_def list;
  }

let initial_env intf_env =
  {
    eval_env = Static_eval.make_env intf_env;
    static_nodes = [];
  }

let add_local_defs env block =
  { env with eval_env = Static_eval.add_local_defs env.eval_env block; }

let add_node_def env nd =
  { env with eval_env = Static_eval.add_node_def env.eval_env nd; }

let add_static_node_def env nd =
  { env with static_nodes = nd :: env.static_nodes; }

let static_nodes env = env.static_nodes

(** {2 Putting it all together} *)

let rec simpl_static_var env v =
  Static_eval.eval_var env.eval_env v

and simpl_clock_exp env ce =
  let ced =
    match ce.ce_desc with
    | Ce_var v ->
      Acids_preclock.Ce_var v
    | Ce_pword pw ->
      let pw =
        Ast_misc.map_upword (simpl_static_exp env) (simpl_static_exp env) pw
      in
      Acids_preclock.Ce_pword pw
    | Ce_equal (ce, se) ->
      let ce = simpl_clock_exp env ce in
      let se = simpl_static_exp env se in
      Acids_preclock.Ce_equal (ce, se)
    | Ce_iter ce ->
      Acids_preclock.Ce_iter (simpl_clock_exp env ce)
  in
  {
    Acids_preclock.ce_desc = ced;
    Acids_preclock.ce_loc = ce.ce_loc;
    Acids_preclock.ce_info = ce.ce_info;
  }

and simpl_static_exp env se =
  let open Acids_scoped.Info in
  let sed =
    match se.se_desc with
    | Se_var v ->
      let ec = get_econstr (simpl_static_var env v) in
      Acids_preclock.Info.Se_econstr ec
    | Se_econstr ec -> Acids_preclock.Info.Se_econstr ec
    | Se_fword fw -> Acids_preclock.Info.Se_fword fw
  in
  {
    Acids_preclock.se_desc = sed;
    Acids_preclock.se_loc = se.se_loc;
    Acids_preclock.se_info = se.se_info;
  }

and simpl_pattern env p =
  let pd =
    match p.p_desc with
    | P_var (v, ita) -> Acids_preclock.P_var (v, ita)
    | P_tuple p_l ->
      Acids_preclock.P_tuple (List.map (simpl_pattern env) p_l)
    | P_clock_annot (p, cka) ->
      let p = simpl_pattern env p in
      let cka = simpl_clock_annot env cka in
      Acids_preclock.P_clock_annot (p, cka)
    | P_type_annot (p, tya) ->
      Acids_preclock.P_type_annot (simpl_pattern env p, tya)
    | P_split pt ->
      let pt =
        Ast_misc.map_upword (simpl_pattern env) (simpl_static_exp env) pt
      in
      Acids_preclock.P_split pt
  in
  {
    Acids_preclock.p_desc = pd;
    Acids_preclock.p_loc = p.p_loc;
    Acids_preclock.p_info = p.p_info;
  }

and simpl_clock_annot env cka =
  match cka with
  | Ca_var v -> Acids_preclock.Ca_var v
  | Ca_on (cka, ce) ->
    let cka = simpl_clock_annot env cka in
    let ce = simpl_clock_exp env ce in
    Acids_preclock.Ca_on (cka, ce)

and simpl_exp env e =
  let ed =
    match e.e_desc with
    | E_var v ->
      Acids_preclock.E_var v
    | E_const c ->
      Acids_preclock.E_const c
    | E_fst e ->
      Acids_preclock.E_fst (simpl_exp env e)
    | E_snd e ->
      Acids_preclock.E_snd (simpl_exp env e)
    | E_tuple e_l ->
      Acids_preclock.E_tuple (List.map (simpl_exp env) e_l)
    | E_fby (e1, e2) ->
      Acids_preclock.E_fby (simpl_exp env e1, simpl_exp env e2)
    | E_ifthenelse (e1, e2, e3) ->
      let e1 = simpl_exp env e1 in
      let e2 = simpl_exp env e2 in
      let e3 = simpl_exp env e3 in
      Acids_preclock.E_ifthenelse (e1, e2, e3)
    | E_app (app, e) ->
      (* TODO: perform inlining *)
      let app =
        {
          Acids_preclock.a_op = app.a_op;
          Acids_preclock.a_loc = app.a_loc;
          Acids_preclock.a_info = app.a_info;
        }
      in
      Acids_preclock.E_app (app, simpl_exp env e)
    | E_where (e, block) ->
      let block, env = simpl_block env block in
      let e = simpl_exp env e in
      Acids_preclock.E_where (e, block)
    | E_when (e, ce) ->
      Acids_preclock.E_when (simpl_exp env e, simpl_clock_exp env ce)
    | E_split (ce, e, ec_l) ->
      Acids_preclock.E_split (simpl_clock_exp env ce, simpl_exp env e, ec_l)
    | E_bmerge (ce, e1, e2) ->
      let ce = simpl_clock_exp env ce in
      let e1 = simpl_exp env e1 in
      let e2 = simpl_exp env e2 in
      Acids_preclock.E_bmerge (ce, e1, e2)
    | E_merge (ce, c_l) ->
      let simpl_clause c =
        {
          Acids_preclock.c_sel = c.c_sel;
          Acids_preclock.c_body = simpl_exp env c.c_body;
          Acids_preclock.c_loc = c.c_loc;
        }
      in
      Acids_preclock.E_merge (simpl_clock_exp env ce, List.map simpl_clause c_l)
    | E_valof ce ->
      Acids_preclock.E_valof (simpl_clock_exp env ce)
    | E_clock_annot (e, cka) ->
      let e = simpl_exp env e in
      let cka = simpl_clock_annot env cka in
      Acids_preclock.E_clock_annot (e, cka)
    | E_type_annot (e, tya) ->
      Acids_preclock.E_type_annot (simpl_exp env e, tya)
    | E_dom (e, dom) ->
      Acids_preclock.E_dom (simpl_exp env e, simpl_domain env dom)
    | E_buffer e ->
      Acids_preclock.E_buffer (simpl_exp env e)
  in
  {
    Acids_preclock.e_desc = ed;
    Acids_preclock.e_loc = e.e_loc;
    Acids_preclock.e_info = e.e_info;
  }

and simpl_block env block =
  let env = add_local_defs env block in
  {
    Acids_preclock.b_body = List.map (simpl_eq env) block.b_body;
    Acids_preclock.b_loc = block.b_loc;
    Acids_preclock.b_info = block.b_info;
  },
  env

and simpl_eq env eq =
  {
    Acids_preclock.eq_lhs = simpl_pattern env eq.eq_lhs;
    Acids_preclock.eq_rhs = simpl_exp env eq.eq_rhs;
    Acids_preclock.eq_loc = eq.eq_loc;
    Acids_preclock.eq_info = eq.eq_info;
  }

and simpl_domain env dom =
  let bck = Utils.map_opt (simpl_clock_annot env) dom.d_base_clock in
  {
    Acids_preclock.d_base_clock = bck;
    Acids_preclock.d_par = dom.d_par;
    Acids_preclock.d_info = dom.d_info;
  }

let simpl_node_def env nd =
  assert (not nd.n_static);
  try
    {
      Acids_preclock.n_name = nd.n_name;
      Acids_preclock.n_input = simpl_pattern env nd.n_input;
      Acids_preclock.n_body = simpl_exp env nd.n_body;
      Acids_preclock.n_pragma = nd.n_pragma;
      Acids_preclock.n_static = nd.n_static;
      Acids_preclock.n_loc = nd.n_loc;
      Acids_preclock.n_info = nd.n_info;
    },
    add_node_def env nd
  with Static_eval.Non_causal v ->
    non_causal nd.n_loc nd.n_name v

let simpl_node_decl nd =
  {
    Acids_preclock.decl_name = nd.decl_name;
    Acids_preclock.decl_data = nd.decl_data;
    Acids_preclock.decl_static = nd.decl_static;
    Acids_preclock.decl_interv = nd.decl_interv;
    Acids_preclock.decl_clock = nd.decl_clock;
    Acids_preclock.decl_loc = nd.decl_loc;
  }

let simpl_type_def td =
  {
    Acids_preclock.ty_name = td.ty_name;
    Acids_preclock.ty_body = td.ty_body;
    Acids_preclock.ty_loc = td.ty_loc;
  }

let simpl_phrase (body, env) phr =
  match phr with
  | Phr_node_def nd ->
    if nd.n_static
    then (body, add_static_node_def env nd)
    else
      let nd, env = simpl_node_def env nd in
      (Acids_preclock.Phr_node_def nd :: body, env)
  | Phr_node_decl nd ->
    (Acids_preclock.Phr_node_decl (simpl_node_decl nd) :: body, env)
  | Phr_type_def td ->
    (Acids_preclock.Phr_type_def (simpl_type_def td) :: body, env)

let simpl_file file =
  let env = initial_env file.f_info#interfaces in
  let body, env = List.fold_left simpl_phrase ([], env) file.f_body in
  let info =
    object
      method interfaces = file.f_info#interfaces
      method static_nodes = static_nodes env
    end
  in
  {
    Acids_preclock.f_name = file.f_name;
    Acids_preclock.f_imports = file.f_imports;
    Acids_preclock.f_info = info;
    Acids_preclock.f_body = body;
  }

let simpl_file
    ctx
    (file : < interfaces : Interface.env > Acids_static.file) =
  ctx, simpl_file file

let simpl =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_preclock.print_file
       "static_simpl"
       simpl_file)
