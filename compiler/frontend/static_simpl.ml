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
    intf_env : Interface.env;
    eval_env : Static_eval.env;
    static_nodes : Acids_static.node_def list;
    static_node_env : Acids_static.node_def Names.ShortEnv.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    eval_env = Static_eval.make_env intf_env;
    static_nodes = [];
    static_node_env = Names.ShortEnv.empty;
  }

let add_local_defs env block =
  { env with eval_env = Static_eval.add_local_defs env.eval_env block; }

let add_node_def env nd =
  { env with eval_env = Static_eval.add_node_def env.eval_env nd; }

let add_static_node_def env nd =
  {
    env with
      static_nodes = nd :: env.static_nodes;
      static_node_env = Names.ShortEnv.add nd.n_name nd env.static_node_env;
  }

let find_static_node_def env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ShortEnv.find ln.shortn env.static_node_env
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    Interface.node_definition_of_node_item (Interface.find_node intf ln.shortn)

let static_nodes env = env.static_nodes

(** {2 Putting it all together} *)

let rec simpl_static_var env v =
  Static_eval.eval_var env.eval_env v

and simpl_clock_exp env ce =
  let ced =
    match ce.ce_desc with
    | Ce_condvar v ->
      Acids_preinter.Ce_condvar v

    | Ce_pword pw ->
      let pw =
        Ast_misc.map_upword (simpl_static_exp env) (simpl_static_exp env) pw
      in
      Acids_preinter.Ce_pword pw

    | Ce_equal (ce, se) ->
      let ce = simpl_clock_exp env ce in
      let se = simpl_static_exp env se in
      Acids_preinter.Ce_equal (ce, se)
  in
  {
    Acids_preinter.ce_desc = ced;
    Acids_preinter.ce_loc = ce.ce_loc;
    Acids_preinter.ce_info = ce.ce_info;
  }

and simpl_static_exp env se =
  let open Acids_scoped.Info in
  let ec =
    match se.se_desc with
    | Se_var v -> get_econstr (simpl_static_var env v)
    | Se_econstr ec -> ec
  in
  {
    Acids_preinter.se_desc = ec;
    Acids_preinter.se_loc = se.se_loc;
    Acids_preinter.se_info = se.se_info;
  }

and simpl_pattern env p =
  let pd =
    match p.p_desc with
    | P_var v -> Acids_preinter.P_var v

    | P_condvar v -> Acids_preinter.P_condvar v

    | P_tuple p_l ->
      Acids_preinter.P_tuple (List.map (simpl_pattern env) p_l)

    | P_clock_annot (p, cka) ->
      let p = simpl_pattern env p in
      let cka = simpl_clock_annot env cka in
      Acids_preinter.P_clock_annot (p, cka)

    | P_type_annot (p, tya) ->
      Acids_preinter.P_type_annot (simpl_pattern env p, tya)

    | P_spec_annot (p, spec) ->
      let p = simpl_pattern env p in
      let spec = simpl_spec env spec in
      Acids_preinter.P_spec_annot (p, spec)

    | P_split pt ->
      let pt =
        Ast_misc.map_upword (simpl_pattern env) (simpl_static_exp env) pt
      in
      Acids_preinter.P_split pt
  in
  {
    Acids_preinter.p_desc = pd;
    Acids_preinter.p_loc = p.p_loc;
    Acids_preinter.p_info = p.p_info;
  }

and simpl_clock_annot env cka =
  match cka with
  | Ca_var v -> Acids_preinter.Ca_var v
  | Ca_on (cka, ce) ->
    let cka = simpl_clock_annot env cka in
    let ce = simpl_clock_exp env ce in
    Acids_preinter.Ca_on (cka, ce)

and simpl_exp env e =
  let ed =
    match e.e_desc with
    | E_var v ->
      Acids_preinter.E_var v

    | E_const c ->
      Acids_preinter.E_const c


    | E_fst e ->
      Acids_preinter.E_fst (simpl_exp env e)

    | E_snd e ->
      Acids_preinter.E_snd (simpl_exp env e)

    | E_tuple e_l ->
      Acids_preinter.E_tuple (List.map (simpl_exp env) e_l)

    | E_fby (e1, e2) ->
      Acids_preinter.E_fby (simpl_exp env e1, simpl_exp env e2)

    | E_ifthenelse (e1, e2, e3) ->
      let e1 = simpl_exp env e1 in
      let e2 = simpl_exp env e2 in
      let e3 = simpl_exp env e3 in
      Acids_preinter.E_ifthenelse (e1, e2, e3)

    | E_app (app, e_arg) ->
      if app.a_info.Info.ai_is_static
      then simpl_inline env app.a_op e e_arg
      else
        let app =
          {
            Acids_preinter.a_op = app.a_op;
            Acids_preinter.a_loc = app.a_loc;
            Acids_preinter.a_info = ();
          }
        in
        Acids_preinter.E_app (app, simpl_exp env e_arg)

    | E_where (e, block) ->
      let block, env = simpl_block env block in
      let e = simpl_exp env e in
      Acids_preinter.E_where (e, block)

    | E_when (e, ce) ->
      Acids_preinter.E_when (simpl_exp env e, simpl_clock_exp env ce)

    | E_split (ce, e, ec_l) ->
      Acids_preinter.E_split (simpl_clock_exp env ce, simpl_exp env e, ec_l)

    | E_bmerge (ce, e1, e2) ->
      let ce = simpl_clock_exp env ce in
      let e1 = simpl_exp env e1 in
      let e2 = simpl_exp env e2 in
      Acids_preinter.E_bmerge (ce, e1, e2)

    | E_merge (ce, c_l) ->
      let simpl_clause c =
        {
          Acids_preinter.c_sel = c.c_sel;
          Acids_preinter.c_body = simpl_exp env c.c_body;
          Acids_preinter.c_loc = c.c_loc;
        }
      in
      Acids_preinter.E_merge (simpl_clock_exp env ce, List.map simpl_clause c_l)

    | E_valof ce ->
      Acids_preinter.E_valof (simpl_clock_exp env ce)

    | E_clock_annot (e, cka) ->
      let e = simpl_exp env e in
      let cka = simpl_clock_annot env cka in
      Acids_preinter.E_clock_annot (e, cka)

    | E_type_annot (e, tya) ->
      Acids_preinter.E_type_annot (simpl_exp env e, tya)

    | E_spec_annot (e, spec) ->
      Acids_preinter.E_spec_annot (simpl_exp env e, simpl_spec env spec)

    | E_dom (e, dom) ->
      Acids_preinter.E_dom (simpl_exp env e, simpl_domain env dom)

    | E_buffer e ->
      Acids_preinter.E_buffer (simpl_exp env e)
  in
  {
    Acids_preinter.e_desc = ed;
    Acids_preinter.e_loc = e.e_loc;
    Acids_preinter.e_info = e.e_info;
  }

and simpl_block env block =
  let env = add_local_defs env block in
  {
    Acids_preinter.b_body = List.map (simpl_eq env) block.b_body;
    Acids_preinter.b_loc = block.b_loc;
    Acids_preinter.b_info = block.b_info;
  },
  env

and simpl_eq env eq =
  {
    Acids_preinter.eq_lhs = simpl_pattern env eq.eq_lhs;
    Acids_preinter.eq_rhs = simpl_exp env eq.eq_rhs;
    Acids_preinter.eq_loc = eq.eq_loc;
    Acids_preinter.eq_info = eq.eq_info;
  }

and simpl_domain env dom =
  let bck = Utils.map_opt (simpl_clock_annot env) dom.d_base_clock in
  {
    Acids_preinter.d_base_clock = bck;
    Acids_preinter.d_par = dom.d_par;
    Acids_preinter.d_info = dom.d_info;
  }

and simpl_inline env ln e_app e_arg =
  (*
    When "f p = e1" is static, we translate "f e2" to
     "e1 where rec p = e2"
  *)
  let nd = find_static_node_def env ln in
  let module R = Acids_utils.REFRESH(Acids_static) in
  let nd = R.refresh_node nd in
  let e =
    {
      e_app with (* keep typing info from e_app *)
      e_desc =
        E_where
          (
            nd.n_body,
            {
              b_body =
                [
                  {
                    eq_lhs = nd.n_input;
                    eq_rhs = e_arg;
                    eq_info = ();
                    eq_loc = Loc.dummy;
                  }
                ];
              b_loc = Loc.dummy;
              b_info = ();
            }
          );
    }
  in
  let e = simpl_exp env e in
  e.Acids_preinter.e_desc

and simpl_spec env spec =
  match spec with
  | Unspec -> Acids_preinter.Unspec
  | Word pw ->
    let simpl_static_exp = simpl_static_exp env in
    let pw =
      Ast_misc.map_upword simpl_static_exp simpl_static_exp pw
    in
    Acids_preinter.Word pw
  | Interval (l, u) ->
    let l = simpl_static_exp env l in
    let u = simpl_static_exp env u in
    Acids_preinter.Interval (l, u)

let simpl_node_def env nd =
  assert (not nd.n_static);
  try
    (* /!\ NEEDED FOR INLINING /!\ *)
    Ident.set_current_ctx nd.n_info#ni_ctx;
    {
      Acids_preinter.n_name = nd.n_name;
      Acids_preinter.n_input = simpl_pattern env nd.n_input;
      Acids_preinter.n_body = simpl_exp env nd.n_body;
      Acids_preinter.n_pragma = nd.n_pragma;
      Acids_preinter.n_static = nd.n_static;
      Acids_preinter.n_loc = nd.n_loc;
      Acids_preinter.n_info = nd.n_info;
    }
  with Static_eval.Non_causal v ->
    non_causal nd.n_loc nd.n_name v

let simpl_node_decl nd =
  {
    Acids_preinter.decl_name = nd.decl_name;
    Acids_preinter.decl_data = nd.decl_data;
    Acids_preinter.decl_static = nd.decl_static;
    Acids_preinter.decl_interv = nd.decl_interv;
    Acids_preinter.decl_clock = nd.decl_clock;
    Acids_preinter.decl_loc = nd.decl_loc;
  }

let simpl_type_def td =
  {
    Acids_preinter.ty_name = td.ty_name;
    Acids_preinter.ty_body = td.ty_body;
    Acids_preinter.ty_loc = td.ty_loc;
  }

let simpl_phrase (body, env) phr =
  match phr with
  | Phr_node_def nd ->
    let body, env =
      if nd.n_static
      then body, add_static_node_def env nd
      else Acids_preinter.Phr_node_def (simpl_node_def env nd) :: body, env
    in
    body, add_node_def env nd

  | Phr_node_decl nd ->
    Acids_preinter.Phr_node_decl (simpl_node_decl nd) :: body, env

  | Phr_type_def td ->
    Acids_preinter.Phr_type_def (simpl_type_def td) :: body, env

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
    Acids_preinter.f_name = file.f_name;
    Acids_preinter.f_imports = file.f_imports;
    Acids_preinter.f_info = info;
    Acids_preinter.f_body = List.rev body;
  }

let simpl_file
    ctx
    (file : < interfaces : Interface.env > Acids_static.file) =
  ctx, simpl_file file

let simpl =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_preinter.print_file
       "static_simpl"
       simpl_file)
