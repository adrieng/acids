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

module type ANNOTATION =
sig
  type new_annot
  val print_new_annot : Format.formatter -> new_annot -> unit
end

module MakeAnnot
  (A : Acids.A)
  (ANN : ANNOTATION)
  =
struct
  type var = A.I.var
  let print_var = A.I.print_var

  type 'a annot = { new_annot : ANN.new_annot; old_annot : 'a; }
  let print_annot
      ?(print_old = false)
      print
      fmt
      { new_annot = na; old_annot = oa; } =
    if print_old
    then
      Format.fprintf fmt "@[ new: %a,@ old: %a@]"
        ANN.print_new_annot na
        print oa
    else
      Format.fprintf fmt " %a" ANN.print_new_annot na

  type clock_exp_info = A.I.clock_exp_info annot
  let print_clock_exp_info = print_annot A.I.print_clock_exp_info

  type static_exp_info = A.I.static_exp_info annot
  let print_static_exp_info = print_annot A.I.print_static_exp_info

  type 'a static_exp_desc = 'a A.I.static_exp_desc
  let print_static_exp_desc = A.I.print_static_exp_desc
  let map_static_exp_desc = A.I.map_static_exp_desc

  type exp_info = A.I.exp_info annot
  let print_exp_info = print_annot A.I.print_exp_info

  type app_info = A.I.app_info annot
  let print_app_info = print_annot A.I.print_app_info

  type block_info = A.I.block_info annot
  let print_block_info = print_annot A.I.print_block_info

  type pat_info = A.I.pat_info annot
  let print_pat_info = print_annot A.I.print_pat_info

  type eq_info = A.I.eq_info annot
  let print_eq_info = print_annot A.I.print_eq_info

  type node_info = A.I.node_info annot
  let print_node_info = print_annot A.I.print_node_info

  type domain_info = A.I.domain_info annot
  let print_domain_info = print_annot A.I.print_domain_info

  type buffer_info = A.I.buffer_info annot
  let print_buffer_info = print_annot A.I.print_buffer_info

  let annotate olda newa = { new_annot = newa; old_annot = olda; }
end

module type INFO_MAP =
sig
  module IN_INFO : Acids.S
  module OUT_INFO : Acids.S

  val update_clock_exp_info : IN_INFO.clock_exp_info -> OUT_INFO.clock_exp_info
  val update_static_exp_info :
    IN_INFO.static_exp_info -> OUT_INFO.static_exp_info
  val update_exp_info : IN_INFO.exp_info -> OUT_INFO.exp_info
  val update_app_info : IN_INFO.app_info -> OUT_INFO.app_info
  val update_block_info : IN_INFO.block_info -> OUT_INFO.block_info
  val update_pat_info : IN_INFO.pat_info -> OUT_INFO.pat_info
  val update_eq_info : IN_INFO.eq_info -> OUT_INFO.eq_info
  val update_domain_info : IN_INFO.domain_info -> OUT_INFO.domain_info
  val update_buffer_info : IN_INFO.buffer_info -> OUT_INFO.buffer_info
  val update_node_info : IN_INFO.node_info -> OUT_INFO.node_info
end

module MakeMap
  (IN : Acids.A)
  (OUT : Acids.A
   with type I.var = IN.I.var
   and type 'a I.static_exp_desc = 'a IN.I.static_exp_desc)
  (M : INFO_MAP with module IN_INFO = IN.I and module OUT_INFO = OUT.I)
  =
struct
  open IN

  let rec extract_clock_exp ce =
    let ced =
      match ce.ce_desc with
      | Ce_condvar v ->
        OUT.Ce_condvar v
      | Ce_pword w ->
        let w = Ast_misc.map_upword extract_static_exp extract_static_exp w in
        OUT.Ce_pword w
      | Ce_equal (ce, se) ->
        OUT.Ce_equal (extract_clock_exp ce, extract_static_exp se)
    in
    {
      OUT.ce_desc = ced;
      OUT.ce_loc = ce.ce_loc;
      OUT.ce_info = M.update_clock_exp_info ce.ce_info;
    }

  and extract_static_exp se =
    {
      OUT.se_desc = IN.I.map_static_exp_desc extract_static_exp se.se_desc;
      OUT.se_loc = se.se_loc;
      OUT.se_info = M.update_static_exp_info se.se_info;
    }

  and extract_exp e =
    let ed =
      match e.e_desc with
      | E_var id -> OUT.E_var id
      | E_const c -> OUT.E_const c
      | E_fst e -> OUT.E_fst (extract_exp e)
      | E_snd e -> OUT.E_snd (extract_exp e)
      | E_tuple e_l -> OUT.E_tuple (List.map extract_exp e_l)
      | E_fby (e1, e2) -> OUT.E_fby (extract_exp e1, extract_exp e2)
      | E_ifthenelse (e1, e2, e3) ->
        OUT.E_ifthenelse (extract_exp e1, extract_exp e2, extract_exp e3)
      | E_app (app, e) -> OUT.E_app (extract_app app, extract_exp e)
      | E_where (e, block) -> OUT.E_where (extract_exp e, extract_block block)
      | E_when (e, ce) -> OUT.E_when (extract_exp e, extract_clock_exp ce)
      | E_split (ce, e, ec_l) ->
        OUT.E_split (extract_clock_exp ce, extract_exp e, ec_l)
      | E_bmerge (ce, e1, e2) ->
        OUT.E_bmerge (extract_clock_exp ce, extract_exp e1, extract_exp e2)
      | E_merge (ce, c_l) ->
        OUT.E_merge (extract_clock_exp ce, List.map extract_merge_clause c_l)
      | E_valof ce ->
        OUT.E_valof (extract_clock_exp ce)
      | E_clock_annot (e, ca) ->
        OUT.E_clock_annot (extract_exp e, extract_clock_annot ca)
      | E_type_annot (e, ty) ->
        OUT.E_type_annot (extract_exp e, ty)
      | E_spec_annot (e, spec) ->
        OUT.E_spec_annot (extract_exp e, extract_spec spec)
      | E_dom (e, dom) ->
        OUT.E_dom (extract_exp e, extract_domain dom)
      | E_buffer (e, bu) ->
        OUT.E_buffer (extract_exp e, extract_buffer bu)
    in
    {
      OUT.e_desc = ed;
      OUT.e_loc = e.e_loc;
      OUT.e_info = M.update_exp_info e.e_info;
    }

  and extract_app app =
    {
      OUT.a_op = app.a_op;
      OUT.a_loc = app.a_loc;
      OUT.a_info = M.update_app_info app.a_info;
    }

  and extract_block block =
    {
      OUT.b_body = List.map extract_eq block.b_body;
      OUT.b_loc = block.b_loc;
      OUT.b_info = M.update_block_info block.b_info;
    }

  and extract_pattern p =
    let pd =
      match p.p_desc with
      | P_var id -> OUT.P_var id
      | P_tuple p_l -> OUT.P_tuple (List.map extract_pattern p_l)
      | P_clock_annot (p, ca) ->
        OUT.P_clock_annot (extract_pattern p, extract_clock_annot ca)
      | P_type_annot (p, ty) ->
        OUT.P_type_annot (extract_pattern p, ty)
      | P_spec_annot (p, spec) ->
        OUT.P_spec_annot (extract_pattern p, extract_spec spec)
      | P_split w ->
        OUT.P_split (Ast_misc.map_upword extract_pattern extract_static_exp w)
    in
    {
      OUT.p_desc = pd;
      OUT.p_loc = p.p_loc;
      OUT.p_info = M.update_pat_info p.p_info;
    }

  and extract_eq eq =
    let desc =
      match eq.eq_desc with
      | Eq_plain (lhs, rhs) ->
        OUT.Eq_plain (extract_pattern lhs, extract_exp rhs)
      | Eq_condvar (lhs, specs, rhs) ->
        OUT.Eq_condvar (lhs, List.map extract_spec specs, extract_exp rhs)
    in
    {
      OUT.eq_desc = desc;
      OUT.eq_loc = eq.eq_loc;
      OUT.eq_info = M.update_eq_info eq.eq_info;
    }

  and extract_merge_clause c =
    {
      OUT.c_sel = c.c_sel;
      OUT.c_body = extract_exp c.c_body;
      OUT.c_loc = c.c_loc;
    }

  and extract_clock_annot ca =
    match ca with
    | Ca_var i -> OUT.Ca_var i
    | Ca_on (ca, ce) -> OUT.Ca_on (extract_clock_annot ca, extract_clock_exp ce)

  and extract_domain dom =
    {
      OUT.d_base_clock = Utils.map_opt extract_clock_annot dom.d_base_clock;
      OUT.d_par = dom.d_par;
      OUT.d_info = M.update_domain_info dom.d_info;
    }

  and extract_buffer bu =
    {
      OUT.bu_info = M.update_buffer_info bu.bu_info;
    }

  and extract_spec spec =
    let sd =
      match spec.s_desc with
      | Unspec -> OUT.Unspec
      | Word w ->
        let w = Ast_misc.map_upword extract_static_exp extract_static_exp w in
        OUT.Word w
      | Interval (l, u) ->
        OUT.Interval (extract_static_exp l, extract_static_exp u)
    in
    {
      OUT.s_desc = sd;
      OUT.s_loc = spec.s_loc;
    }

  and extract_node_def nd =
    {
      OUT.n_name = nd.n_name;
      OUT.n_input = extract_pattern nd.n_input;
      OUT.n_body = extract_exp nd.n_body;
      OUT.n_pragma = nd.n_pragma;
      OUT.n_static = nd.n_static;
      OUT.n_loc = nd.n_loc;
      OUT.n_info = M.update_node_info nd.n_info;
    }

  and extract_node_decl nd =
    {
      OUT.decl_name = nd.decl_name;
      OUT.decl_data = nd.decl_data;
      OUT.decl_static = nd.decl_static;
      OUT.decl_clock = nd.decl_clock;
      OUT.decl_loc = nd.decl_loc;
    }

  and extract_type_def td =
    {
      OUT.ty_name = td.ty_name;
      OUT.ty_body = td.ty_body;
      OUT.ty_loc = td.ty_loc;
    }

  let extract_static_def sd =
    {
      OUT.sd_name = sd.sd_name;
      OUT.sd_var = sd.sd_var;
      OUT.sd_body = extract_exp sd.sd_body;
      OUT.sd_loc = sd.sd_loc;
    }

  let extract_phrase phr =
    match phr with
    | Phr_node_def nd -> OUT.Phr_node_def (extract_node_def nd)
    | Phr_node_decl nd -> OUT.Phr_node_decl (extract_node_decl nd)
    | Phr_type_def td -> OUT.Phr_type_def (extract_type_def td)
    | Phr_static_def sd -> OUT.Phr_static_def (extract_static_def sd)

  let extract_file f =
    {
      OUT.f_name = f.f_name;
      OUT.f_imports = f.f_imports;
      OUT.f_info = f.f_info;
      OUT.f_body = List.map extract_phrase f.f_body;
    }
end

module FREEVARS(A : Acids.A
                with type I.var = Ident.t
                and type
                  'a I.static_exp_desc =
                       'a Acids_prespec.Info.static_exp_desc) =
struct
  open A

  (* TODO: we currently do not consider static exps *)

  let rec fv_clock_exp fv ce =
    match ce.ce_desc with
    | Ce_condvar v -> Ident.Set.add v fv
    | Ce_pword _ -> fv
    | Ce_equal (ce, _) -> fv_clock_exp fv ce

  and fv_exp fv e =
    match e.e_desc with
    | E_var v -> Ident.Set.add v fv

    | E_const _ -> fv

    | E_fst e | E_snd e | E_app (_, e)
    | E_type_annot (e, _) | E_buffer (e, _) -> fv_exp fv e

    | E_tuple e_l -> List.fold_left fv_exp fv e_l

    | E_fby (e1, e2) -> fv_exp (fv_exp fv e1) e2

    | E_ifthenelse (e1, e2, e3) -> fv_exp (fv_exp (fv_exp fv e1) e2) e3

    | E_where (e, block) ->
      let fv = fv_exp fv e in
      let fv, bv = fv_block fv block in
      Ident.Set.diff fv bv

    | E_when (e, ce) | E_split (ce, e, _) -> fv_exp (fv_clock_exp fv ce) e

    | E_bmerge (ce, e1, e2) -> fv_exp (fv_exp (fv_clock_exp fv ce) e1) e2

    | E_merge (ce, c_l) ->
      List.fold_left (fun fv c -> fv_exp fv c.c_body) (fv_clock_exp fv ce) c_l

    | E_valof ce -> fv_clock_exp fv ce

    | E_clock_annot (e, cka) ->
      fv_exp (fv_clock_annot fv cka) e

    | E_spec_annot (e, spec) ->
      fv_exp (fv_spec fv spec) e

    | E_dom (e, dom) ->
      let fv =
        match dom.d_base_clock with
        | None -> fv
        | Some cka -> fv_clock_annot fv cka
      in
      fv_exp fv e

  and fv_clock_annot fv cka =
    match cka with
    | Ca_var _ -> fv
    | Ca_on (cka, ce) -> fv_clock_annot (fv_clock_exp fv ce) cka

  and fv_pattern ?(gather_clock_vars = true) fv p =
    match p.p_desc with
    | P_var v -> Ident.Set.add v fv
    | P_tuple p_l -> List.fold_left fv_pattern fv p_l
    | P_clock_annot (p, cka) ->
      let fv =
        if gather_clock_vars
        then fv_clock_annot fv cka
        else fv
      in
      fv_pattern fv p
    | P_type_annot (p, _) -> fv_pattern fv p
    | P_spec_annot (p, _) -> fv_pattern fv p
    | P_split pw ->
      Ast_misc.fold_upword (Utils.flip fv_pattern) (fun _ l -> l) pw fv

  and fv_spec fv spec =
    match spec.s_desc with
    | Unspec -> fv
    | Word _ -> fv
    | Interval _ -> fv

  and fv_block fv block =
    let bv_eq bv eq =
      match eq.eq_desc with
      | Eq_plain (lhs, _) -> fv_pattern ~gather_clock_vars:false bv lhs
      | Eq_condvar (lhs, _, _) -> Ident.Set.add lhs bv
    in
    let fv_eq fv eq =
      match eq.eq_desc with
      | Eq_plain (_, rhs) | Eq_condvar (_, _, rhs) -> fv_exp fv rhs
    in

    let fv = List.fold_left fv_eq fv block.b_body in
    let bv = List.fold_left bv_eq Ident.Set.empty block.b_body in
    fv, bv
end

module REFRESH(A : Acids.A
               with type I.var = Ident.t
               and type
                 'a I.static_exp_desc = 'a Acids_scoped.Info.static_exp_desc) =
struct
  open A

  let refresh_var env v =
    try env, Ident.Env.find v env
    with Not_found ->
      let v' = Ident.refresh v in
      Ident.Env.add v v' env, v'

  let rec refresh_clock_exp ce env =
    let ced, env =
      match ce.ce_desc with
      | Ce_condvar v ->
        let env, v = refresh_var env v in
        Ce_condvar v, env
      | Ce_pword pw ->
        let pw, env =
          Ast_misc.mapfold_upword refresh_static_exp refresh_static_exp pw env
        in
        Ce_pword pw, env
      | Ce_equal (ce, se) ->
        let ce, env = refresh_clock_exp ce env in
        let se, env = refresh_static_exp se env in
        Ce_equal (ce, se), env
    in
    { ce with ce_desc = ced; }, env

  and refresh_static_exp se env =
    let open Acids_scoped.Info in
    let sed, env =
      match se.se_desc with
      | Se_var v ->
        let env, v = refresh_var env v in
        Se_var v, env
      | Se_econstr _ -> se.se_desc, env
      | Se_binop (op, se1, se2) ->
        let se1, env = refresh_static_exp se1 env in
        let se2, env = refresh_static_exp se2 env in
        Se_binop (op, se1, se2), env
    in
    { se with se_desc = sed; }, env

  and refresh_clock_annot cka env =
    match cka with
    | Ca_var _ -> cka, env
    | Ca_on (cka, ce) ->
      let cka, env = refresh_clock_annot cka env in
      let ce, env = refresh_clock_exp ce env in
      Ca_on (cka, ce), env

  and refresh_exp e env =
    let ed, env =
      match e.e_desc with
      | E_var v ->
        let env, v = refresh_var env v in
        E_var v, env

      | E_const c ->
        E_const c, env

      | E_fst e ->
        let e, env = refresh_exp e env in
        E_fst e, env

      | E_snd e ->
        let e, env = refresh_exp e env in
        E_snd e, env

      | E_tuple e_l ->
        let e_l, env = Utils.mapfold refresh_exp e_l env in
        E_tuple e_l, env

      | E_fby (e1, e2) ->
        let e1, env = refresh_exp e1 env in
        let e2, env = refresh_exp e2 env in
        E_fby (e1, e2), env

      | E_ifthenelse (e1, e2, e3) ->
        let e1, env = refresh_exp e1 env in
        let e2, env = refresh_exp e2 env in
        let e3, env = refresh_exp e3 env in
        E_ifthenelse (e1, e2, e3), env

      | E_app (app, e) ->
        let e, env = refresh_exp e env in
        E_app (app, e), env

      | E_where (e, block) ->
        let e, env = refresh_exp e env in
        let block, env = refresh_block block env in
        E_where (e, block), env

      | E_when (e, ce) ->
        let e, env = refresh_exp e env in
        let ce, env = refresh_clock_exp ce env in
        E_when (e, ce), env

      | E_split (ce, e, ec_l) ->
        let ce, env = refresh_clock_exp ce env in
        let e, env = refresh_exp e env in
        E_split (ce, e, ec_l), env

      | E_bmerge (ce, e1, e2) ->
        let ce, env = refresh_clock_exp ce env in
        let e1, env = refresh_exp e1 env in
        let e2, env = refresh_exp e2 env in
        E_bmerge (ce, e1, e2), env

      | E_merge (ce, c_l) ->
        let ce, env = refresh_clock_exp ce env in
        let refresh_clause c env =
          let body, env = refresh_exp c.c_body env in
          { c with c_body = body; }, env
        in
        let c_l, env = Utils.mapfold refresh_clause c_l env in
        E_merge (ce, c_l), env

      | E_valof ce ->
        let ce, env = refresh_clock_exp ce env in
        E_valof ce, env

      | E_clock_annot (e, cka) ->
        let e, env = refresh_exp e env in
        let cka, env = refresh_clock_annot cka env in
        E_clock_annot (e, cka), env

      | E_type_annot (e, tya) ->
        let e, env = refresh_exp e env in
        E_type_annot (e, tya), env

      | E_spec_annot (e, spec) ->
        let e, env = refresh_exp e env in
        let spec, env = refresh_spec spec env in
        E_spec_annot (e, spec), env

      | E_dom (e, dom) ->
        let e, env = refresh_exp e env in
        let dom, env = refresh_domain dom env in
        E_dom (e, dom), env

      | E_buffer (e, bu) ->
        let e, env = refresh_exp e env in
        E_buffer (e, bu), env
    in
    { e with e_desc = ed; }, env

  and refresh_domain dom env =
    let cka, env = Utils.mapfold_opt refresh_clock_annot dom.d_base_clock env in
    { dom with d_base_clock = cka; }, env

  and refresh_spec spec env =
    let sd, env =
      match spec.s_desc with
      | Unspec -> Unspec, env
      | Word pw ->
        let pw, env =
          Ast_misc.mapfold_upword refresh_static_exp refresh_static_exp pw env
        in
        Word pw, env
      | Interval (l, u) ->
        let l, env = refresh_static_exp l env in
        let u, env = refresh_static_exp u env in
        Interval (l, u), env
    in
    {
      s_desc = sd;
      s_loc = spec.s_loc;
    },
    env

  and refresh_block block env =
    let body, env = Utils.mapfold refresh_eq block.b_body env in
    { block with b_body = body; }, env

  and refresh_eq eq env =
    let desc, env =
      match eq.eq_desc with
      | Eq_plain (lhs, rhs) ->
        let lhs, env = refresh_pattern lhs env in
        let rhs, env = refresh_exp rhs env in
        Eq_plain (lhs, rhs), env
      | Eq_condvar (lhs, specs, rhs) ->
        let env, lhs = refresh_var env lhs in
        let specs, env = Utils.mapfold refresh_spec specs env in
        let rhs, env = refresh_exp rhs env in
        Eq_condvar (lhs, specs, rhs), env
    in
    { eq with eq_desc = desc; }, env

  and refresh_pattern p env =
    let pd, env =
      match p.p_desc with
      | P_var v ->
        let env, v = refresh_var env v in
        P_var v, env

      | P_tuple p_l ->
        let p_l, env = Utils.mapfold refresh_pattern p_l env in
        P_tuple p_l, env

      | P_clock_annot (p, cka) ->
        let p, env = refresh_pattern p env in
        let cka, env = refresh_clock_annot cka env in
        P_clock_annot (p, cka), env

      | P_type_annot (p, tya) ->
        let p, env = refresh_pattern p env in
        P_type_annot (p, tya), env

      | P_spec_annot (p, spec) ->
        let p, env = refresh_pattern p env in
        let spec, env = refresh_spec spec env in
        P_spec_annot (p, spec), env

      | P_split pt ->
        let pt, env =
          Ast_misc.mapfold_upword refresh_pattern refresh_static_exp pt env
        in
        P_split pt, env
    in
    { p with p_desc = pd; }, env

  let refresh_node nd =
    let input, env = refresh_pattern nd.n_input Ident.Env.empty in
    let body, _ = refresh_exp nd.n_body env in
    { nd with n_input = input; n_body = body; }
end

module DEP_GRAPH
  (
    A : Acids.A
   with type I.var = Ident.t
   and type 'a I.static_exp_desc = 'a Acids_prespec.Info.static_exp_desc
  ) =
struct
  module G = Graph.Imperative.Digraph.ConcreteBidirectional(Ident)
  module FV = FREEVARS(A)

  open A

  type env =
    {
      graph : G.t;
      mutable id_env : G.vertex Ident.Env.t;
      current_lhs : G.vertex list;
      relevant_exp : exp -> bool;
    }

  let find_vtx env v =
    try Ident.Env.find v env.id_env
    with Not_found ->
      let vtx = G.V.create v in
      G.add_vertex env.graph vtx;
      env.id_env <- Ident.Env.add v vtx env.id_env;
      vtx

  let add_var env v =
    let src_vtx = find_vtx env v in
    let add_edge dst_vtx = G.add_edge env.graph src_vtx dst_vtx in
    List.iter add_edge env.current_lhs

  let rec dep_graph_clock_exp env ce =
    match ce.ce_desc with
    | Ce_condvar v -> add_var env v
    | Ce_pword _ -> ()
    | Ce_equal (ce, _) -> dep_graph_clock_exp env ce

  let rec dep_graph_exp env e =
    if env.relevant_exp e
    then
      match e.e_desc with
      | E_var v ->
        add_var env v

      | E_const _ ->
        ()

      | E_fst e | E_snd e | E_app (_, e)
      | E_clock_annot (e, _) | E_type_annot (e, _) | E_spec_annot (e, _)
      | E_dom (e, _) | E_buffer (e, _)
        ->
        dep_graph_exp env e

      | E_tuple e_l ->
        List.iter (dep_graph_exp env) e_l

      | E_fby (e1, e2) ->
        dep_graph_exp env e1;
        dep_graph_exp env e2

      | E_ifthenelse (e1, e2, e3) ->
        dep_graph_exp env e1;
        dep_graph_exp env e2;
        dep_graph_exp env e3

      | E_where (e, block) ->
        dep_graph_exp env e;
        dep_graph_block env block

      | E_when (e, ce) ->
        dep_graph_exp env e;
        dep_graph_clock_exp env ce

      | E_split (ce, e, _) ->
        dep_graph_clock_exp env ce;
        dep_graph_exp env e

      | E_bmerge (ce, e1, e2) ->
        dep_graph_clock_exp env ce;
        dep_graph_exp env e1;
        dep_graph_exp env e2

      | E_merge (ce, c_l) ->
        dep_graph_clock_exp env ce;
        List.iter (fun c -> dep_graph_exp env c.c_body) c_l

      | E_valof ce ->
        dep_graph_clock_exp env ce

  and dep_graph_eq env eq =
    let lhs_v, rhs =
      match eq.eq_desc with
      | Eq_plain (lhs, rhs) -> FV.fv_pattern Ident.Set.empty lhs, rhs
      | Eq_condvar (lhs, _, rhs) -> Ident.Set.singleton lhs, rhs
    in
    let env =
      let add v env =
        let vtx = find_vtx env v in
        { env with current_lhs = vtx :: env.current_lhs; }
      in
      Ident.Set.fold add lhs_v { env with current_lhs = []; }
    in
    dep_graph_exp env rhs

  and dep_graph_block env block =
    List.iter (dep_graph_eq env) block.b_body

  let dep_graph relevant_exp e =
    let env =
      {
        graph = G.create ~size:10 ();
        id_env = Ident.Env.empty;
        current_lhs = [];
        relevant_exp = relevant_exp;
      }
    in
    dep_graph_exp env e;
    env.graph
end
