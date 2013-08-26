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

(** {1 surface syntax to NIR translation}

    This pass translates lowered Acids_causal to NIR.
*)

open Acids_causal

(** {2 Utilities} *)

let non_lowered feat = Compiler.internal_error (feat ^ " was not lowered")

let translate_static_exp se = se.se_desc

let translate_static_exp_int se = Ast_misc.get_int (translate_static_exp se)

let translate_static_pword pw =
  Tree_word.map_upword translate_static_exp translate_static_exp_int pw

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    local_pwords : Ast_misc.static_pword Names.ShortEnv.t;
    current_block : int;
    current_locals : unit Nir.var_dec Ident.Env.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    local_pwords = Names.ShortEnv.empty;
    current_block = 0;
    current_locals = Ident.Env.empty;
  }

let add_pword env pn pw =
  let p = translate_static_pword pw in
  { env with local_pwords = Names.ShortEnv.add pn p env.local_pwords; }

let find_pword env ln =
  let open Names in
  match ln.modn with
  | LocalModule ->
    ShortEnv.find ln.shortn env.local_pwords
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    Interface.((find_pword intf ln.shortn).pi_value)

let get_current_block env = Nir.Block_id (env.current_block)

let get_current_block_count env = succ env.current_block

let increment_current_block env =
  { env with current_block = succ env.current_block; }

let add_local env vd =
  {
    env with
      current_locals = Ident.Env.add vd.Nir.v_name vd env.current_locals;
  }

let get_locals env = env.current_locals

(** {2 Translation of expressions} *)

let translate_data_type ty =
  let open Data_types in
  match ty with
  | Ty_var i -> Nir.Ty_var i
  | Ty_scal tys | Ty_cond tys -> Nir.Ty_scal tys
  | Ty_prod _ -> invalid_arg "translate_data_type: product type"

let translate_stream_type _ st =
  Nir.Ck_stream st

let translate_clock_type env ct =
  let open Clock_types in
  match ct with
  | Ct_var i -> Nir.Ck_var i
  | Ct_stream st -> translate_stream_type env st
  | Ct_prod _ -> invalid_arg "translate_clock_type: product clock"

let rec translate_clock_exp env ce =
  let ced =
    match ce.ce_desc with
    | Ce_condvar v ->
      Nir.Ce_condvar v
    | Ce_pword (Pd_lit pw) ->
      Nir.Ce_pword (translate_static_pword pw)
    | Ce_pword (Pd_global ln) ->
      Nir.Ce_pword (find_pword env ln)
    | Ce_equal (ce, se) ->
      Nir.Ce_equal (translate_clock_exp env ce, translate_static_exp se)
  in
  {
    Nir.ce_desc = ced;
    Nir.ce_data = ce.ce_info#ci_data;
    Nir.ce_clock = translate_stream_type env ce.ce_info#ci_clock;
    Nir.ce_bounds = ce.ce_info#ci_bounds;
    Nir.ce_loc = ce.ce_loc;
  }

(* Translates a Nir.clock_exp to Clock_types.clock_exp *)
let rec clock_clock_exp_of_clock_exp ce =
  let open Clock_types in
  match ce.Nir.ce_desc with
  | Nir.Ce_condvar id ->
    let cev =
      {
        cecv_name = id;
        cecv_bounds = ce.Nir.ce_bounds;
        cecv_specs = []; (* TODO reconstruct from Eq_condvar *)
      }
    in
    Ce_condvar cev
  | Nir.Ce_pword p ->
    Ce_pword p
  | Nir.Ce_equal (ce, ec) ->
    Ce_equal (clock_clock_exp_of_clock_exp ce, ec)

let translate_clock_annot env cka =
  let rec walk cka =
    match cka with
    | Ca_var i ->
      (* TODO is this reasonable? *)
      Clock_types.St_var i
    | Ca_on (cka, ce) ->
      let ce = translate_clock_exp env ce in
      Clock_types.St_on (walk cka, clock_clock_exp_of_clock_exp ce)
  in
  Nir.Ck_stream (walk cka)

let translate_spec spec =
  match spec.s_desc with
  | Unspec ->
    invalid_arg "translate_spec: Unspec"
  | Word pw ->
    let p =
      Tree_word.map_upword translate_static_exp_int translate_static_exp_int pw
    in
    Ast_misc.Word p
  | Interval (l, u) ->
    let l = translate_static_exp_int l in
    let u = translate_static_exp_int u in
    Ast_misc.Interval (Interval.make l u)

let rec translate_pattern p (env, v_l) =
  match p.p_desc with
  | P_clock_annot _ | P_spec_annot _ | P_type_annot _ | P_var _ ->
    let rec get_annots annots p =
      match p.p_desc with
      | P_var v ->
        v, annots
      | P_clock_annot (p, cka) ->
        let ann = Nir.Ann_clock (translate_clock_annot env cka) in
        get_annots (ann :: annots) p
      | P_type_annot (p, tya) ->
        let ann = Nir.Ann_type (translate_data_type tya) in
        get_annots (ann :: annots) p
      | P_spec_annot (p, { s_desc = Unspec; }) ->
        get_annots annots p
      | P_spec_annot (p, spec) ->
        get_annots (Nir.Ann_spec (translate_spec spec) :: annots) p
      | P_split _ ->
        non_lowered "P_split"
      | P_tuple _ ->
        non_lowered "P_tuple inside annotations"
    in
    let v, annots = get_annots [] p in
    let vd =
      {
        Nir.v_name = v;
        Nir.v_data = translate_data_type p.p_info#pi_data;
        Nir.v_clock = translate_clock_type env p.p_info#pi_clock;
        Nir.v_scope = Nir.Scope_internal (get_current_block env);
        Nir.v_annots = annots;
        Nir.v_loc = p.p_loc;
        Nir.v_info = ();
      }
    in
    add_local env vd, v :: v_l
  | P_tuple p_l ->
    List.fold_right translate_pattern p_l (env, v_l)
  | P_split _ ->
    non_lowered "P_split"

let var_list_of_tuple e =
  let rec walk e v_l =
    match e.e_desc with
    | E_var v -> v :: v_l
    | E_tuple e_l -> List.fold_right walk e_l v_l
    | _ -> invalid_arg "var_list_of_tuple: not a variable or tuple"
  in
  walk e []

let rec translate_eq_exp env x_l e =
  let eqd, bck, env =
    match e.e_desc with
    | E_var y ->
      Nir.Var (Utils.get_single x_l, y),
      translate_clock_type env e.e_info#ei_clock,
      env

    | E_const cst ->
      Nir.Const (Utils.get_single x_l, cst),
      translate_clock_type env e.e_info#ei_clock,
      env

    | E_fst _ | E_snd _ ->
      non_lowered "projection"

    | E_tuple _ ->
      non_lowered "tuple"

    | E_fby _ ->
      non_lowered "fby"

    | E_ifthenelse _ ->
      non_lowered "ifthenelse"

    | E_app (app, e) ->
      let inst = app.a_info#ai_clock_inst in
      let op =
        let open Names in
        match app.a_op.modn with
        | Module "Pervasives" -> Nir.Builtin app.a_op.shortn
        | _ -> Nir.Node app.a_op
      in
      Nir.Call (x_l,
                Nir.({ a_op = op; a_clock_inst = inst; }),
                var_list_of_tuple e),
      Nir.Ck_block_base,
      env

    | E_where _ ->
      non_lowered "where (subexps)"

    | E_when (e, ce) ->
      (*
        x = y when ce
        ->
        (x, wh) = split y with ce by true, false

        where "wh" is fresh in the node
      *)
      let x = Utils.get_single x_l in
      let y = Utils.get_single (var_list_of_tuple e) in
      let nir_ce = translate_clock_exp env ce in
      let v_unused = Ident.make_internal "wh" in
      let vd =
        let open Nir in
        let st =
          Clock_types.St_on (ce.ce_info#ci_clock,
                             clock_clock_exp_of_clock_exp nir_ce)
        in
        {
          v_name = v_unused;
          v_data = translate_data_type e.e_info#ei_data;
          v_clock = Ck_stream st;
          v_scope = Scope_internal (get_current_block env);
          v_info = ();
          v_annots = [];
          v_loc = Loc.dummy;
        }
      in
      Nir.Split ([x; v_unused],
                 nir_ce,
                 y,
                 Ast_misc.([Ec_bool true; Ec_bool false])),
      nir_ce.Nir.ce_clock,
      add_local env vd

    | E_split (ce, e, ec_l) ->
      let y = Utils.get_single (var_list_of_tuple e) in
      let ce = translate_clock_exp env ce in
      Nir.Split (x_l, ce, y, ec_l),
      ce.Nir.ce_clock,
      env

    | E_bmerge (ce, e1, e2) ->
      let x = Utils.get_single x_l in
      let y1 = Utils.get_single (var_list_of_tuple e1) in
      let y2 = Utils.get_single (var_list_of_tuple e2) in
      let ce = translate_clock_exp env ce in
      Nir.Merge (x,
                 ce,
                 [ Ast_misc.Ec_bool true, y1; Ast_misc.Ec_bool false, y2; ]),
      ce.Nir.ce_clock,
      env

    | E_merge (ce, c_l) ->
      let x = Utils.get_single x_l in
      let translate_clause c =
        c.c_sel, Utils.get_single (var_list_of_tuple c.c_body)
      in
      let ce = translate_clock_exp env ce in
      Nir.Merge (x,
                 ce,
                 List.map translate_clause c_l),
      ce.Nir.ce_clock,
      env

    | E_valof ce ->
      let ce = translate_clock_exp env ce in
      Nir.Valof (Utils.get_single x_l, ce),
      ce.Nir.ce_clock,
      env

    | E_dom (e, dom) ->
      let block, _, env = translate_block env e in
      Nir.Block block,
      translate_stream_type env dom.d_info,
      env

    | E_buffer (e', bu) ->
      let y = Utils.get_single (var_list_of_tuple e') in
      let bu =
        {
          Nir.b_delay = bu.bu_info#bui_is_delay;
          Nir.b_size = bu.bu_info#bui_size;
        }
      in
      Nir.Buffer (Utils.get_single x_l, bu, y),
      Nir.Ck_block_base,
      env

    (* For now we do nothing with the annotations. *)
    | E_clock_annot (e, _) | E_type_annot (e, _) | E_spec_annot (e, _) ->
      Nir.Var (Utils.get_single x_l, Utils.get_single (var_list_of_tuple e)),
      translate_clock_type env e.e_info#ei_clock,
      env
  in
  env,
  {
    Nir.eq_desc = eqd;
    Nir.eq_base_clock = bck;
    Nir.eq_loc = e.e_loc;
  }

and translate_eq env eq =
  match eq.eq_desc with
  | Eq_condvar _ ->
    failwith "unimplemented" (* TODO with cond var rework *)
  | Eq_plain (p, e) ->
    let env, v_l = translate_pattern p (env, []) in
    translate_eq_exp env v_l e

and translate_block env e =
  match e.e_desc with
  | E_where (out, block) ->
    let env, body = Utils.mapfold_left translate_eq env block.b_body in
    {
      Nir.b_id = get_current_block env;
      Nir.b_body = body;
      Nir.b_loc = e.e_loc;
    },
    var_list_of_tuple out,
    env
  | _ ->
    non_lowered "where (subexps)"

(** {2 Translation of nodes and types definitions, and files} *)

let translate_node_def env nd =
  Ident.set_current_ctx nd.n_info#ni_ctx;
  let env, inputs = translate_pattern nd.n_input (env, []) in
  let block, outputs, env = translate_block env nd.n_body in
  {
    Nir.n_name = nd.n_name;
    Nir.n_input = inputs;
    Nir.n_output = outputs;
    Nir.n_env = get_locals env;
    Nir.n_block_count = get_current_block_count env;
    Nir.n_body = block;
    Nir.n_loc = nd.n_loc;
  }

let translate_type_def td =
  {
    Nir.ty_name = td.ty_name;
    Nir.ty_body = td.ty_body;
    Nir.ty_loc = td.ty_loc;
  }

let translate_phrase phr (type_defs, node_defs, env) =
  match phr with
  | Phr_static_def _ | Phr_node_decl _ ->
    type_defs, node_defs, env
  | Phr_pword_def pd ->
    type_defs, node_defs, add_pword env pd.pd_name pd.pd_body
  | Phr_node_def nd ->
    type_defs, translate_node_def env nd :: node_defs, env
  | Phr_type_def td ->
    translate_type_def td :: type_defs, node_defs, env

let file ctx (file : Acids_causal_utils.annotated_file) =
  let env = initial_env file.f_info#interfaces in
  let type_defs, node_defs, _ =
    List.fold_right translate_phrase file.f_body ([], [], env)
  in
  let nir_file : unit Nir.file =
    {
      Nir.f_name = file.f_name;
      Nir.f_interfaces = file.f_info#interfaces;
      Nir.f_type_defs = type_defs;
      Nir.f_body = node_defs;
    }
  in
  ctx, nir_file

(** {2 Putting it all together} *)

let pass =
  let open Pass_manager in
  P_transform
    (make_transform
       ~ext:"nir"
       ~print_out:Nir_printer.print_file
       "nir_of_acids"
       file)
