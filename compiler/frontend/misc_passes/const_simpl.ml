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

open Acids_const

(** {2 Exceptions} *)

type error =
  | Non_causal of Loc.t * Names.shortname * Ident.t
  | Negative_pword of
      Loc.t *
      (Acids_prespec.const_exp, Acids_prespec.const_exp) Tree_word.t
  | Unimplemented_builtin of Loc.t * Names.longname

exception Simplification_error of error

let print_error fmt err =
  match err with
  | Non_causal (l, nn, v) ->
    Format.fprintf fmt
      "%aConst variable %a in node %a is defined in terms of itself"
      Loc.print l
      Ident.print v
      Names.print_shortname nn
  | Negative_pword (l, p) ->
    Format.fprintf fmt
      "%aThe expression %a should be positive"
      Loc.print l
      Acids_prespec.print_const_word p
  | Unimplemented_builtin (loc, ln) ->
    Format.fprintf fmt
      "%aThe built-in function %a is not currently implemented"
      Loc.print loc
      Names.print_longname ln

let non_causal loc nn v =
  raise (Simplification_error (Non_causal (loc, nn, v)))

let negative_pword loc ce =
  raise (Simplification_error (Negative_pword (loc, ce)))

let unimplemented_builtin loc ln =
  raise (Simplification_error (Unimplemented_builtin (loc, ln)))

(** {2 Utility functions} *)

let get_econstr value =
  let open Const_eval in
  let open Ast_misc in
  match value with
  | Const (Cconstr ec) -> ec
  | _ -> invalid_arg "get_econstr"

let get_int value =
  let open Const_eval in
  let open Ast_misc in
  match value with
  | Const (Cconstr (Ec_int i)) -> i
  | _ -> invalid_arg "get_int"

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    eval_env : Const_eval.env;
    const_nodes : Acids_const.node_def list;
    const_node_env : Acids_const.node_def Names.ShortEnv.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    eval_env = Const_eval.make_env intf_env;
    const_nodes = [];
    const_node_env = Names.ShortEnv.empty;
  }

let add_local_defs env block =
  { env with eval_env = Const_eval.add_local_defs env.eval_env block; }

let add_node_def env nd =
  { env with eval_env = Const_eval.add_node_def env.eval_env nd; }

let add_const_node_def env nd =
  {
    env with
      const_nodes = nd :: env.const_nodes;
      const_node_env = Names.ShortEnv.add nd.n_name nd env.const_node_env;
  }

let add_const_var env var value =
  {
    env with
      eval_env = Const_eval.add_const env.eval_env var value;
  }

let add_pword env var body =
  {
    env with
      eval_env = Const_eval.add_pword env.eval_env var body;
  }

let find_const_node_def env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ShortEnv.find ln.shortn env.const_node_env
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    Interface.node_definition_of_node_item (Interface.find_node intf ln.shortn)

let const_nodes env = env.const_nodes

(** {2 Putting it all together} *)

let rec simpl_const_var env v =
  Const_eval.eval_var env.eval_env v

and simpl_const_word env loc pw =
  let pw =
    Tree_word.map_upword (simpl_const_exp env) (simpl_const_exp env) pw
  in

  let check_pos se =
    let open Ast_misc in
    match se.Acids_prespec.se_desc with
    | Ec_int i when i < Int.zero -> negative_pword loc pw
    | _ -> ()
  in
  Tree_word.iter_upword check_pos (fun _ -> ()) pw;
  pw

and simpl_clock_exp env ce =
  let ced =
    match ce.ce_desc with
    | Ce_condvar v ->
      Acids_prespec.Ce_condvar v

    | Ce_pword (Pd_lit pw) ->
      let pw = simpl_const_word env ce.ce_loc pw in
      Acids_prespec.Ce_pword (Acids_prespec.Pd_lit pw)

    | Ce_pword (Pd_global ln) ->
      Acids_prespec.Ce_pword (Acids_prespec.Pd_global ln)

    | Ce_equal (ce, se) ->
      let ce = simpl_clock_exp env ce in
      let se = simpl_const_exp env se in
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

and simpl_const_exp env se =
  let open Const_eval in
  let ec =
    match eval_const_exp env.eval_env se with
    | Const (Ast_misc.Cconstr ec) -> ec
    | _ -> invalid_arg "ill-typed"
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

    (* | P_condvar (v, specs) -> *)
    (*   let specs = List.map (simpl_spec env) specs in *)
    (*   Acids_prespec.P_condvar (v, specs) *)

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
        Tree_word.map_upword (simpl_pattern env) (simpl_const_exp env) pt
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
      if app.a_info.Info.ai_is_const
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

    | E_buffer (e, bu) ->
      Acids_prespec.E_buffer (simpl_exp env e, simpl_buffer env bu)
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
  let desc =
    match eq.eq_desc with
    | Eq_plain (lhs, rhs) ->
      Acids_prespec.Eq_plain (simpl_pattern env lhs, simpl_exp env rhs)
    | Eq_condvar (lhs, specs, rhs) ->
      let specs = List.map (simpl_spec env) specs in
      let rhs = simpl_exp env rhs in
      Acids_prespec.Eq_condvar (lhs, specs, rhs)
  in
  {
    Acids_prespec.eq_desc = desc;
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

and simpl_buffer _ bu =
  {
    Acids_prespec.bu_info = bu.bu_info;
  }

and simpl_inline env ln e_app e_arg =
  (*
    When "f p = e" is const, we translate "f e_arg" to
     "e where rec p = e_arg"
  *)
  let nd = find_const_node_def env ln in
  let module R = Acids_utils.REFRESH(Acids_const) in
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
                    eq_desc = Eq_plain (nd.n_input, e_arg);
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
      let simpl_const_exp = simpl_const_exp env in
      let pw =
        Tree_word.map_upword simpl_const_exp simpl_const_exp pw
      in
      Acids_prespec.Word pw
    | Interval (l, u) ->
      let l = simpl_const_exp env l in
      let u = simpl_const_exp env u in
      Acids_prespec.Interval (l, u)
  in
  {
    Acids_prespec.s_desc = sd;
    Acids_prespec.s_loc = spec.s_loc;
  }

let simpl_node_def env nd =
  assert (not nd.n_const);
  try
    (* /!\ NEEDED FOR INLINING /!\ *)
    Ident.set_current_ctx nd.n_info#ni_ctx;
    {
      Acids_prespec.n_name = nd.n_name;
      Acids_prespec.n_input = simpl_pattern env nd.n_input;
      Acids_prespec.n_body = simpl_exp env nd.n_body;
      Acids_prespec.n_pragma = nd.n_pragma;
      Acids_prespec.n_const = nd.n_const;
      Acids_prespec.n_loc = nd.n_loc;
      Acids_prespec.n_info =
        object
          method ni_ctx = nd.n_info#ni_ctx
          method ni_data = nd.n_info#ni_data
          method ni_const = nd.n_info#ni_const
        end;
    }
  with
  | Const_eval.Error (Const_eval.Non_causal v) ->
    non_causal nd.n_loc nd.n_name v
  | Const_eval.Error (Const_eval.Unimplemented_builtin (loc, ln)) ->
    unimplemented_builtin loc ln

let simpl_node_decl nd =
  {
    Acids_prespec.decl_name = nd.decl_name;
    Acids_prespec.decl_data = nd.decl_data;
    Acids_prespec.decl_const = nd.decl_const;
    Acids_prespec.decl_clock = nd.decl_clock;
    Acids_prespec.decl_loc = nd.decl_loc;
  }

let simpl_const_def env sd =
  let open Const_eval in
  let c =
    let res = eval_exp env.eval_env sd.sd_body in
    match res with
    | Const c -> c
    | _ -> assert false (* const-typing error? *)
  in
  {
    Acids_prespec.sd_name = sd.sd_name;
    Acids_prespec.sd_body =
      {
        Acids_prespec.e_desc = Acids_prespec.E_const c;
        Acids_prespec.e_info =
          object
            method ei_data = sd.sd_body.e_info#ei_data
          end;
        Acids_prespec.e_loc = sd.sd_body.e_loc;
      };
    Acids_prespec.sd_loc = sd.sd_loc;
  },
  add_const_var env sd.sd_name (Const c)

let simpl_pword_def env pd =
  let body = simpl_const_word env pd.pd_loc pd.pd_body in
  {
    Acids_prespec.pd_name = pd.pd_name;
    Acids_prespec.pd_body = body;
    Acids_prespec.pd_loc = pd.pd_loc;
  },
  add_pword env pd.pd_name pd.pd_body

let simpl_phrase (body, env) phr =
  match phr with
  | Phr_node_def nd ->
    let body, env =
      if nd.n_const
      then body, add_const_node_def env nd
      else Acids_prespec.Phr_node_def (simpl_node_def env nd) :: body, env
    in
    body, add_node_def env nd

  | Phr_node_decl nd ->
    Acids_prespec.Phr_node_decl (simpl_node_decl nd) :: body, env

  | Phr_type_def td ->
    Acids_prespec.Phr_type_def td :: body, env

  | Phr_const_def sd ->
    let sd, env = simpl_const_def env sd in
    Acids_prespec.Phr_const_def sd :: body, env

  | Phr_pword_def pd ->
    let pd, env = simpl_pword_def env pd in
    Acids_prespec.Phr_pword_def pd :: body, env

let simpl_file file =
  let env = initial_env file.f_info#interfaces in
  let body, env = List.fold_left simpl_phrase ([], env) file.f_body in
  let info =
    object
      method interfaces = file.f_info#interfaces
      method const_nodes = const_nodes env
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
    (file : < interfaces : Interface.env > Acids_const.file) =
  ctx, simpl_file file

let pass =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_prespec.print_file
       "const_simpl"
       simpl_file)
