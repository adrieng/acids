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

(** {1 surface syntax to NIR translation}

    This pass translates lowered Acids_causal to NIR.
*)

open Acids_causal

(** {2 Utilities} *)

let non_lowered feat = Compiler.internal_error (feat ^ " was not lowered")

let const_of_const_exp se = se.se_desc

let int_of_const_exp se = Ast_misc.get_int (const_of_const_exp se)

let translate_const_pword pw =
  Tree_word.map_upword const_of_const_exp int_of_const_exp pw

let st_base =
  Clock_types.St_var Nir_acids.Info.Cv_base

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    local_pwords : Ast_misc.const_pword Names.ShortEnv.t;
    current_block : int;
    current_locals : Nir_acids.var_dec Ident.Env.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    local_pwords = Names.ShortEnv.empty;
    current_block = 0;
    current_locals = Ident.Env.empty;
  }

let add_pword env pn pw =
  let p = translate_const_pword pw in
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

let get_current_scope env = Nir_acids.Scope_internal (get_current_block env)

let increment_current_block env =
  { env with current_block = succ env.current_block; }

let add_local env vd =
  {
    env with
      current_locals = Ident.Env.add vd.Nir_acids.v_name vd env.current_locals;
  }

let get_locals env = env.current_locals

let get_var_clock env x =
  (Ident.Env.find x env.current_locals).Nir_acids.v_clock

(** {2 Translation of expressions} *)

let translate_data_type ty =
  let open Data_types in
  match ty with
  | Ty_var i -> Nir.Ty_var i
  | Ty_scal tys | Ty_cond tys -> Nir.Ty_scal tys
  | Ty_boxed _ -> Nir.Ty_boxed
  | Ty_prod _ -> invalid_arg "translate_data_type: product type"

let rec translate_stream_type (st : Clock_types.stream_type) =
  let open Clock_types in
  match st with
  | St_var i -> St_var (Nir_acids.Info.Cv_clock i)
  | St_on (st, ce) -> St_on (translate_stream_type st, ce)

let translate_clock_type ct =
  let open Clock_types in
  match ct with
  | Ct_stream st -> translate_stream_type st
  | Ct_prod _ -> invalid_arg "translate_clock_type: product clock"

let translate_const_exp env eql se =
  let x = Ident.make_internal "se" in
  let vd =
    Nir_acids.make_var_dec
      ~loc:se.se_loc
      x
      (Nir.Ty_scal se.se_info#pwi_data)
      (translate_stream_type se.se_info#pwi_clock)
      (get_current_scope env)
  in
  let eq =
    Nir_acids.make_eq
      ~loc:se.se_loc
      (Nir_acids.Const (x, Ast_misc.Cconstr se.se_desc))
      (translate_stream_type se.se_info#pwi_clock)
  in
  add_local env vd,
  eq :: eql,
  x

let rec translate_clock_exp env eql ce =
  match ce.ce_desc with
  | Ce_condvar v ->
    env, eql, v
  | Ce_pword _ | Ce_equal _ ->
    let x = Ident.make_internal "ce" in
    let clock = translate_stream_type ce.ce_info#ci_clock in
    let vd =
      Nir_acids.make_var_dec
        ~loc:ce.ce_loc
        ~annots:[Nir_acids.Ann_spec (Ast_misc.Interval ce.ce_info#ci_bounds)]
        x
        (Nir.Ty_scal ce.ce_info#ci_data)
        clock
        (get_current_scope env)
    in
    let env, eql, eq =
      let env, eql, eqd =
        match ce.ce_desc with
        | Ce_condvar _ ->
          assert false (* handled above *)
        | Ce_pword (Pd_lit pw) ->
          env, eql, Nir_acids.Pword (x, translate_const_pword pw)
        | Ce_pword (Pd_global ln) ->
          env, eql, Nir_acids.Pword (x, find_pword env ln)
        | Ce_equal (ce, se) ->
          let env, eql, x_ce = translate_clock_exp env eql ce in
          let env, eql, x_se = translate_const_exp env eql se in
          let call =
            let open Nir_acids in
            {
              a_op = Node Names.(make_longname (Module "Pervasives") "=");
              a_stream_inst = [0, ce.ce_info#ci_clock];
            }
          in
          env, eql, Nir_acids.Call ([x], call, [x_ce; x_se])
      in
      env,
      eql,
      Nir_acids.make_eq
        ~loc:ce.ce_loc
        eqd
        clock
    in
    add_local env vd, eq :: eql, x

(* Translates a Acids_causal.clock_exp to Clock_types.clock_exp *)
let rec clock_clock_exp_of_clock_exp env ce =
  let open Clock_types in
  match ce.ce_desc with
  | Acids_causal.Ce_condvar id ->
    let cev =
      {
        cecv_name = id;
        cecv_bounds = ce.Acids_causal.ce_info#ci_bounds;
        cecv_specs = []; (* TODO reconstruct from Eq_condvar *)
      }
    in
    Ce_condvar cev
  | Acids_causal.Ce_pword (Acids_causal.Pd_lit pw) ->
    Ce_pword (translate_const_pword pw)
  | Acids_causal.Ce_pword (Acids_causal.Pd_global ln) ->
    Ce_pword (find_pword env ln)
  | Acids_causal.Ce_equal (ce, se) ->
    Ce_equal (clock_clock_exp_of_clock_exp env ce, se.se_desc)

let translate_clock_annot env cka =
  let rec walk cka =
    match cka with
    | Ca_var i ->
      Clock_types.St_var (Nir_acids.Info.Cv_clock i)
    | Ca_on (cka, ce) ->
      Clock_types.St_on (walk cka, clock_clock_exp_of_clock_exp env ce)
  in
  walk cka

let translate_spec spec =
  match spec.s_desc with
  | Unspec ->
    invalid_arg "translate_spec: Unspec"
  | Word pw ->
    let p =
      Tree_word.map_upword int_of_const_exp int_of_const_exp pw
    in
    Ast_misc.Word p
  | Interval (l, u) ->
    let l = int_of_const_exp l in
    let u = int_of_const_exp u in
    Ast_misc.Interval (Interval.make l u)

let rec translate_pattern p (env, v_l) =
  match p.p_desc with
  | P_clock_annot _ | P_spec_annot _ | P_type_annot _ | P_var _ ->
    let rec get_annots annots p =
      match p.p_desc with
      | P_var v ->
        v, annots
      | P_clock_annot (p, cka) ->
        let ann = Nir_acids.Ann_clock (translate_clock_annot env cka) in
        get_annots (ann :: annots) p
      | P_type_annot (p, tya) ->
        let ann = Nir_acids.Ann_type (translate_data_type tya) in
        get_annots (ann :: annots) p
      | P_spec_annot (p, { s_desc = Unspec; }) ->
        get_annots annots p
      | P_spec_annot (p, spec) ->
        get_annots (Nir_acids.Ann_spec (translate_spec spec) :: annots) p
      | P_split _ ->
        non_lowered "P_split"
      | P_tuple _ ->
        non_lowered "P_tuple inside annotations"
    in
    let v, annots = get_annots [] p in
    let ty = translate_data_type p.p_info#pi_data in
    let ck = translate_clock_type p.p_info#pi_clock in
    let vd =
      Nir_acids.make_var_dec
        ~loc:p.p_loc
        ~annots
        v
        ty
        ck
        (get_current_scope env)
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

let rec translate_eq_exp (env, eql) x_l e =
  match e.e_desc with
  | E_valof ce ->
    let env, eql, _ = translate_clock_exp env eql ce in
    env,
    eql
  | _ ->
    let eqd, bck, env, eql =
      match e.e_desc with
      | E_var y ->
        Nir_acids.Var (Utils.get_single x_l, y),
        translate_clock_type e.e_info#ei_clock,
        env,
        eql

      | E_const cst ->
        Nir_acids.Const (Utils.get_single x_l, cst),
        translate_clock_type e.e_info#ei_clock,
        env,
        eql

      | E_fst _ | E_snd _ ->
        non_lowered "projection"

      | E_tuple _ ->
        non_lowered "tuple"

      | E_fby _ ->
        non_lowered "fby"

      | E_ifthenelse _ ->
        non_lowered "ifthenelse"

      | E_app (app, e) ->
        let app =
          {
            Nir_acids.a_op =
              (
                let open Names in
                match app.a_op.modn, app.a_op.shortn with
                | Module "Pervasives", "box" ->
                  Nir_acids.Box
                | Module "Pervasives", "unbox" ->
                  Nir_acids.Unbox
                | _ ->
                  Nir_acids.Node app.a_op
              );
            Nir_acids.a_stream_inst = app.a_info#ai_stream_inst;
          }
        in
        Nir_acids.Call (x_l, app, var_list_of_tuple e),
        st_base,
        env,
        eql

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
        let env, eql, nir_ce = translate_clock_exp env eql ce in
        let clock = get_var_clock env nir_ce in
        let v_unused = Ident.make_internal "wh" in
        let vd =
          let st =
            Clock_types.St_on (ce.ce_info#ci_clock,
                               assert false (* TODO *))
          in
          Nir_acids.make_var_dec
            v_unused
            (translate_data_type e.e_info#ei_data)
            (translate_stream_type st)
            (get_current_scope env)
        in
        Nir_acids.Split ([x; v_unused],
                         nir_ce,
                         y,
                         Ast_misc.([Ec_bool true; Ec_bool false])),
        clock,
        add_local env vd,
        eql

      | E_split (ce, e, ec_l) ->
        let y = Utils.get_single (var_list_of_tuple e) in
        let env, eql, ce = translate_clock_exp env eql ce in
        Nir_acids.Split (x_l, ce, y, ec_l),
        get_var_clock env ce,
        env,
        eql

      | E_bmerge (ce, e1, e2) ->
        let x = Utils.get_single x_l in
        let y1 = Utils.get_single (var_list_of_tuple e1) in
        let y2 = Utils.get_single (var_list_of_tuple e2) in
        let env, eql, ce = translate_clock_exp env eql ce in
        Nir_acids.Merge (x,
                         ce,
                         [
                           Ast_misc.Ec_bool true, y1;
                           Ast_misc.Ec_bool false, y2;
                         ]),
        get_var_clock env ce,
        env,
        eql

      | E_merge (ce, c_l) ->
        let x = Utils.get_single x_l in
        let translate_clause c =
          c.c_sel, Utils.get_single (var_list_of_tuple c.c_body)
        in
        let env, eql, ce = translate_clock_exp env eql ce in
        Nir_acids.Merge (x,
                         ce,
                         List.map translate_clause c_l),
        get_var_clock env ce,
        env,
        eql

      | E_valof _ ->
        (* Handled above *)
        assert false

      | E_dom (e, dom) ->
        let block, _, env = translate_block env e in
        Nir_acids.Block block,
        translate_stream_type dom.d_info#di_activation_clock,
        env,
        eql

      | E_buffer (e', bu) ->
        let y = Utils.get_single (var_list_of_tuple e') in
        let bu =
          {
            Nir.b_delay = bu.bu_info#bui_is_delay;
            Nir.b_real_size = bu.bu_info#bui_real_size;
            Nir.b_size = bu.bu_info#bui_size;
          }
        in
        Nir_acids.Buffer (Utils.get_single x_l, bu, y),
        st_base,
        env,
        eql

      (* For now we do nothing with the annotations. *)
      | E_clock_annot (e, _) | E_type_annot (e, _) | E_spec_annot (e, _) ->
        Nir_acids.Var (Utils.get_single x_l,
                       Utils.get_single (var_list_of_tuple e)),
        translate_clock_type e.e_info#ei_clock,
        env,
        eql
    in
    env,
    Nir_acids.make_eq
      ~loc:e.e_loc
      eqd
      bck
    :: eql

and translate_eq (env, eql) eq =
  match eq.eq_desc with
  | Eq_condvar _ ->
    failwith "unimplemented" (* TODO with cond var rework *)
  | Eq_plain (p, e) ->
    let env, v_l = translate_pattern p (env, []) in
    translate_eq_exp (env, eql) v_l e

and translate_block env e =
  match e.e_desc with
  | E_where (out, block) ->
    let env, body = List.fold_left translate_eq (env, []) block.b_body in
    Nir_acids.make_block
      ~loc:e.e_loc
      (get_current_block env)
      body,
    var_list_of_tuple out,
    env
  | _ ->
    non_lowered "where (subexps)"

(** {2 Translation of nodes and types definitions, and files} *)

let translate_node_def env nd =
  Ident.set_current_ctx nd.n_info#ni_ctx;
  let env, input = translate_pattern nd.n_input (env, []) in
  let block, output, env = translate_block env nd.n_body in
  Nir_acids.make_node
    ~loc:nd.n_loc
    (Initial.longname_of_shortname_current_module nd.n_name)
    nd.n_info
    ~input
    ~output
    ~env:(get_locals env)
    ~body:block

let translate_type_def td =
  {
    Nir.ty_name = td.ty_name;
    Nir.ty_body = td.ty_body;
    Nir.ty_loc = td.ty_loc;
  }

let translate_phrase (type_defs, node_defs, env) phr =
  match phr with
  | Phr_const_def _ | Phr_node_decl _ ->
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
    List.fold_left translate_phrase ([], [], env) file.f_body
  in
  let nir_file : Interface.env Nir_acids.file =
    {
      Nir_acids.f_name = file.f_name;
      Nir_acids.f_type_defs = List.rev type_defs;
      Nir_acids.f_body = List.rev node_defs;
      Nir_acids.f_info = file.f_info#interfaces;
    }
  in
  ctx, nir_file

(** {2 Putting it all together} *)

module U = Middleend_utils.Make(Nir_acids)(Nir_acids)
let pass = U.make_transform "nir_of_acids" file
