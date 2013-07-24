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
  | Negative_pword of
      Loc.t *
      (Acids_prespec.static_exp, Acids_prespec.static_exp) Tree_word.t

exception Simplification_error of error

let print_error fmt err =
  match err with
  | Non_causal (l, nn, v) ->
    Format.fprintf fmt
      "%aStatic variable %a in node %a is defined in terms of itself"
      Loc.print l
      Ident.print v
      Names.print_shortname nn
  | Negative_pword (l, p) ->
    Format.fprintf fmt
      "%aThe expression %a should be positive"
      Loc.print l
      Acids_prespec.print_static_word p

let non_causal loc nn v =
  raise (Simplification_error (Non_causal (loc, nn, v)))

let negative_pword loc ce =
  raise (Simplification_error (Negative_pword (loc, ce)))

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
      Acids_prespec.Ce_condvar v

    | Ce_pword pw ->
      let pw =
        Ast_misc.map_upword (simpl_static_exp env) (simpl_static_exp env) pw
      in

      let check_pos se =
        let i = Ast_misc.get_int se.Acids_prespec.se_desc in
        if i < Int.zero then negative_pword ce.ce_loc pw
      in
      Tree_word.iter_upword check_pos (fun _ -> ()) pw;

      Acids_prespec.Ce_pword pw

    | Ce_equal (ce, se) ->
      let ce = simpl_clock_exp env ce in
      let se = simpl_static_exp env se in
      Acids_prespec.Ce_equal (ce, se)
  in
  {
    Acids_prespec.ce_desc = ced;
    Acids_prespec.ce_loc = ce.ce_loc;
    Acids_prespec.ce_info =
      object
        method ci_data = ce.ce_info#ci_data;
      end
  }

and simpl_static_exp env se =
  let open Acids_scoped.Info in
  let ec =
    match se.se_desc with
    | Se_var v -> get_econstr (simpl_static_var env v)
    | Se_econstr ec -> ec
  in
  {
    Acids_prespec.se_desc = ec;
    Acids_prespec.se_loc = se.se_loc;
    Acids_prespec.se_info =
      object
        method pwi_data = se.se_info#pwi_data;
      end
  }

and simpl_pattern env p =
  let pd =
    match p.p_desc with
    | P_var v -> Acids_prespec.P_var v

    | P_condvar (v, specs) ->
      let specs = List.map (simpl_spec env) specs in
      Acids_prespec.P_condvar (v, specs)

    | P_tuple p_l ->
      Acids_prespec.P_tuple (List.map (simpl_pattern env) p_l)

    | P_clock_annot (p, cka) ->
      let p = simpl_pattern env p in
      let cka = simpl_clock_annot env cka in
      Acids_prespec.P_clock_annot (p, cka)

    | P_type_annot (p, tya) ->
      Acids_prespec.P_type_annot (simpl_pattern env p, tya)

    | P_spec_annot (p, spec) ->
      let p = simpl_pattern env p in
      let spec = simpl_spec env spec in
      Acids_prespec.P_spec_annot (p, spec)

    | P_split pt ->
      let pt =
        Ast_misc.map_upword (simpl_pattern env) (simpl_static_exp env) pt
      in
      Acids_prespec.P_split pt
  in
  {
    Acids_prespec.p_desc = pd;
    Acids_prespec.p_loc = p.p_loc;
    Acids_prespec.p_info =
      object
        method pi_data = p.p_info#pi_data
      end;
  }

and simpl_clock_annot env cka =
  match cka with
  | Ca_var v -> Acids_prespec.Ca_var v
  | Ca_on (cka, ce) ->
    let cka = simpl_clock_annot env cka in
    let ce = simpl_clock_exp env ce in
    Acids_prespec.Ca_on (cka, ce)

and simpl_exp env e =
  let ed =
    match e.e_desc with
    | E_var v ->
      Acids_prespec.E_var v

    | E_const c ->
      Acids_prespec.E_const c


    | E_fst e ->
      Acids_prespec.E_fst (simpl_exp env e)

    | E_snd e ->
      Acids_prespec.E_snd (simpl_exp env e)

    | E_tuple e_l ->
      Acids_prespec.E_tuple (List.map (simpl_exp env) e_l)

    | E_fby (e1, e2) ->
      Acids_prespec.E_fby (simpl_exp env e1, simpl_exp env e2)

    | E_ifthenelse (e1, e2, e3) ->
      let e1 = simpl_exp env e1 in
      let e2 = simpl_exp env e2 in
      let e3 = simpl_exp env e3 in
      Acids_prespec.E_ifthenelse (e1, e2, e3)

    | E_app (app, e_arg) ->
      if app.a_info.Info.ai_is_static
      then simpl_inline env app.a_op e e_arg
      else
        let app =
          {
            Acids_prespec.a_op = app.a_op;
            Acids_prespec.a_loc = app.a_loc;
            Acids_prespec.a_info = ();
          }
        in
        Acids_prespec.E_app (app, simpl_exp env e_arg)

    | E_where (e, block) ->
      let block, env = simpl_block env block in
      let e = simpl_exp env e in
      Acids_prespec.E_where (e, block)

    | E_when (e, ce) ->
      Acids_prespec.E_when (simpl_exp env e, simpl_clock_exp env ce)

    | E_split (ce, e, ec_l) ->
      Acids_prespec.E_split (simpl_clock_exp env ce, simpl_exp env e, ec_l)

    | E_bmerge (ce, e1, e2) ->
      let ce = simpl_clock_exp env ce in
      let e1 = simpl_exp env e1 in
      let e2 = simpl_exp env e2 in
      Acids_prespec.E_bmerge (ce, e1, e2)

    | E_merge (ce, c_l) ->
      let simpl_clause c =
        {
          Acids_prespec.c_sel = c.c_sel;
          Acids_prespec.c_body = simpl_exp env c.c_body;
          Acids_prespec.c_loc = c.c_loc;
        }
      in
      Acids_prespec.E_merge (simpl_clock_exp env ce, List.map simpl_clause c_l)

    | E_valof ce ->
      Acids_prespec.E_valof (simpl_clock_exp env ce)

    | E_clock_annot (e, cka) ->
      let e = simpl_exp env e in
      let cka = simpl_clock_annot env cka in
      Acids_prespec.E_clock_annot (e, cka)

    | E_type_annot (e, tya) ->
      Acids_prespec.E_type_annot (simpl_exp env e, tya)

    | E_spec_annot (e, spec) ->
      Acids_prespec.E_spec_annot (simpl_exp env e, simpl_spec env spec)

    | E_dom (e, dom) ->
      Acids_prespec.E_dom (simpl_exp env e, simpl_domain env dom)

    | E_buffer e ->
      Acids_prespec.E_buffer (simpl_exp env e)
  in
  {
    Acids_prespec.e_desc = ed;
    Acids_prespec.e_loc = e.e_loc;
    Acids_prespec.e_info =
      object
        method ei_data = e.e_info#ei_data
      end;
  }

and simpl_block env block =
  let env = add_local_defs env block in
  {
    Acids_prespec.b_body = List.map (simpl_eq env) block.b_body;
    Acids_prespec.b_loc = block.b_loc;
    Acids_prespec.b_info = block.b_info;
  },
  env

and simpl_eq env eq =
  {
    Acids_prespec.eq_lhs = simpl_pattern env eq.eq_lhs;
    Acids_prespec.eq_rhs = simpl_exp env eq.eq_rhs;
    Acids_prespec.eq_loc = eq.eq_loc;
    Acids_prespec.eq_info = eq.eq_info;
  }

and simpl_domain env dom =
  let bck = Utils.map_opt (simpl_clock_annot env) dom.d_base_clock in
  {
    Acids_prespec.d_base_clock = bck;
    Acids_prespec.d_par = dom.d_par;
    Acids_prespec.d_info = dom.d_info;
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
  e.Acids_prespec.e_desc

and simpl_spec env spec =
  let sd =
    match spec.s_desc with
    | Unspec -> Acids_prespec.Unspec
    | Word pw ->
      let simpl_static_exp = simpl_static_exp env in
      let pw =
        Ast_misc.map_upword simpl_static_exp simpl_static_exp pw
      in
      Acids_prespec.Word pw
    | Interval (l, u) ->
      let l = simpl_static_exp env l in
      let u = simpl_static_exp env u in
      Acids_prespec.Interval (l, u)
  in
  {
    Acids_prespec.s_desc = sd;
    Acids_prespec.s_loc = spec.s_loc;
  }

let simpl_node_def env nd =
  assert (not nd.n_static);
  try
    (* /!\ NEEDED FOR INLINING /!\ *)
    Ident.set_current_ctx nd.n_info#ni_ctx;
    {
      Acids_prespec.n_name = nd.n_name;
      Acids_prespec.n_input = simpl_pattern env nd.n_input;
      Acids_prespec.n_body = simpl_exp env nd.n_body;
      Acids_prespec.n_pragma = nd.n_pragma;
      Acids_prespec.n_static = nd.n_static;
      Acids_prespec.n_loc = nd.n_loc;
      Acids_prespec.n_info =
        object
          method ni_ctx = nd.n_info#ni_ctx
          method ni_data = nd.n_info#ni_data
        end;
    }
  with Static_eval.Non_causal v ->
    non_causal nd.n_loc nd.n_name v

let simpl_node_decl nd =
  {
    Acids_prespec.decl_name = nd.decl_name;
    Acids_prespec.decl_data = nd.decl_data;
    Acids_prespec.decl_static = nd.decl_static;
    Acids_prespec.decl_clock = nd.decl_clock;
    Acids_prespec.decl_loc = nd.decl_loc;
  }

let simpl_type_def td =
  {
    Acids_prespec.ty_name = td.ty_name;
    Acids_prespec.ty_body = td.ty_body;
    Acids_prespec.ty_loc = td.ty_loc;
  }

let simpl_phrase (body, env) phr =
  match phr with
  | Phr_node_def nd ->
    let body, env =
      if nd.n_static
      then body, add_static_node_def env nd
      else Acids_prespec.Phr_node_def (simpl_node_def env nd) :: body, env
    in
    body, add_node_def env nd

  | Phr_node_decl nd ->
    Acids_prespec.Phr_node_decl (simpl_node_decl nd) :: body, env

  | Phr_type_def td ->
    Acids_prespec.Phr_type_def (simpl_type_def td) :: body, env

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
    Acids_prespec.f_name = file.f_name;
    Acids_prespec.f_imports = file.f_imports;
    Acids_prespec.f_info = info;
    Acids_prespec.f_body = List.rev body;
  }

let simpl_file
    ctx
    (file : < interfaces : Interface.env > Acids_static.file) =
  ctx, simpl_file file

let simpl =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_prespec.print_file
       "static_simpl"
       simpl_file)
