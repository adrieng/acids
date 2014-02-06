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

(* {2 Errors} *)

type error =
  | Instantaneous_dep of Ident.t * Loc.t

exception Causality_error of error

let print_error fmt err =
  match err with
  | Instantaneous_dep (v, l) ->
    Format.fprintf fmt "%aVariable %a instantaneously depends on itself"
      Loc.print l
      Ident.print v

let instantaneous_dep v l =
  raise (Causality_error (Instantaneous_dep (v, l)))

(* {2 Causality check} *)

module DG = Acids_utils.DEP_GRAPH(Acids_causal)
module DFS = Graph.Traverse.Dfs(DG.G)
module SCC = Graph.Components.Make(DG.G)

let check_causal loc e =
  let open Acids_causal in
  let g = DG.dep_graph (fun e -> e.e_info#ei_relevant_deps) e in

  let check_scc scc =
    if List.length scc > 1
    then instantaneous_dep (DG.G.V.label (List.hd scc)) loc
    else
      let vtx = List.hd scc in
      (* check if there's a self-cycle *)
      DG.G.iter_succ
        (fun out_vtx ->
          if DG.G.V.equal vtx out_vtx
          then instantaneous_dep (DG.G.V.label vtx) loc)
        g
        vtx
  in

  if DFS.has_cycle g then List.iter check_scc (SCC.scc_list g)

(* {2 Annotation with dependency info} *)

open Acids_clocked

let annot_exp_info e rel =
  {
    e with
      Acids_causal.e_info =
        object
          method ei_data = e.Acids_causal.e_info#ei_data
          method ei_clock = e.Acids_causal.e_info#ei_clock
          method ei_relevant_deps = rel
        end;
  }

let rec annot_clock_exp ce =
  let ced =
    match ce.ce_desc with
    | Ce_condvar v ->
      Acids_causal.Ce_condvar v
    | Ce_pword (Pd_lit pw) ->
      Acids_causal.Ce_pword (Acids_causal.Pd_lit (annot_const_word pw))
    | Ce_pword (Pd_global ln) ->
      Acids_causal.Ce_pword (Acids_causal.Pd_global ln)
    | Ce_equal (ce, se) ->
      Acids_causal.Ce_equal (annot_clock_exp ce, annot_const_exp se)
  in
  {
    Acids_causal.ce_desc = ced;
    Acids_causal.ce_loc = ce.ce_loc;
    Acids_causal.ce_info = ce.ce_info;
  }

and annot_const_word pw =
  Tree_word.map_upword annot_const_exp annot_const_exp pw

and annot_const_exp se =
  {
    Acids_causal.se_desc = se.se_desc;
    Acids_causal.se_loc = se.se_loc;
    Acids_causal.se_info = se.se_info;
  }

let rec annot_exp e =
  let ed =
    match e.e_desc with
    | E_var v ->
      Acids_causal.E_var v

    | E_const c ->
      Acids_causal.E_const c

    | E_fst e ->
      Acids_causal.E_fst (annot_exp e)

    | E_snd e ->
      Acids_causal.E_snd (annot_exp e)

    | E_tuple e_l ->
      Acids_causal.E_tuple (List.map annot_exp e_l)

    | E_fby (e1, e2) ->
      let rel_e2 = not (Clock_types.binary_clock_type e1.e_info#ei_clock) in
      Acids_causal.E_fby (annot_exp e1, annot_exp_info (annot_exp e2) rel_e2)

    | E_ifthenelse (e1, e2, e3) ->
      Acids_causal.E_ifthenelse (annot_exp e1, annot_exp e2, annot_exp e3)

    | E_app (app, e) ->
      Acids_causal.E_app (annot_app app, annot_exp e)

    | E_where (e, block) ->
      Acids_causal.E_where (annot_exp e, annot_block block)

    | E_when (e, ce) ->
      Acids_causal.E_when (annot_exp e, annot_clock_exp ce)

    | E_split (ce, e, ec_l) ->
      Acids_causal.E_split (annot_clock_exp ce, annot_exp e, ec_l)

    | E_bmerge (ce, e1, e2) ->
      Acids_causal.E_bmerge (annot_clock_exp ce, annot_exp e1, annot_exp e2)

    | E_merge (ce, c_l) ->
      let annot_clause c =
        {
          Acids_causal.c_sel = c.c_sel;
          Acids_causal.c_body = annot_exp c.c_body;
          Acids_causal.c_loc = c.c_loc;
        }
      in
      Acids_causal.E_merge (annot_clock_exp ce, List.map annot_clause c_l)

    | E_valof ce ->
      Acids_causal.E_valof (annot_clock_exp ce)

    | E_clock_annot (e, cka) ->
      Acids_causal.E_clock_annot (annot_exp e, annot_clock_annot cka)

    | E_type_annot (e, tya) ->
      Acids_causal.E_type_annot (annot_exp e, tya)

    | E_spec_annot (e, spec) ->
      Acids_causal.E_spec_annot (annot_exp e, annot_spec spec)

    | E_dom (e, dom) ->
      (* TODO *)
      Acids_causal.E_dom (annot_exp e, annot_dom dom)

    | E_buffer (e, bu) ->
      let e_rel = not (bu.bu_info#bui_is_delay) in
      let e = annot_exp e in
      Acids_causal.E_buffer (annot_exp_info e e_rel, annot_buffer bu)
  in
  {
    Acids_causal.e_desc = ed;
    Acids_causal.e_loc = e.e_loc;
    Acids_causal.e_info =
      object
        method ei_data = e.e_info#ei_data
        method ei_clock = e.e_info#ei_clock
        method ei_relevant_deps = true
      end;
  }

and annot_app app =
  {
    Acids_causal.a_op = app.a_op;
    Acids_causal.a_loc = app.a_loc;
    Acids_causal.a_info = app.a_info;
  }

and annot_block block =
  {
    Acids_causal.b_body = List.map annot_eq block.b_body;
    Acids_causal.b_loc = block.b_loc;
    Acids_causal.b_info = block.b_info;
  }

and annot_eq eq =
  let desc =
    match eq.eq_desc with
    | Eq_plain (lhs, rhs) ->
      Acids_causal.Eq_plain (annot_pattern lhs, annot_exp rhs)
    | Eq_condvar (lhs, specs, rhs) ->
      Acids_causal.Eq_condvar (lhs, List.map annot_spec specs, annot_exp rhs)
  in
  {
    Acids_causal.eq_desc = desc;
    Acids_causal.eq_loc = eq.eq_loc;
    Acids_causal.eq_info = eq.eq_info;
  }

and annot_pattern p =
  let pd =
    match p.p_desc with
    | P_var v ->
      Acids_causal.P_var v
    | P_tuple p_l ->
      Acids_causal.P_tuple (List.map annot_pattern p_l)
    | P_clock_annot (p, cka) ->
      Acids_causal.P_clock_annot (annot_pattern p, annot_clock_annot cka)
    | P_type_annot (p, tya) ->
      Acids_causal.P_type_annot (annot_pattern p, tya)
    | P_spec_annot (p, spec) ->
      Acids_causal.P_spec_annot (annot_pattern p, annot_spec spec)
    | P_split pw ->
      let pw = Tree_word.map_upword annot_pattern annot_const_exp pw in
      Acids_causal.P_split pw
  in
  {
    Acids_causal.p_desc = pd;
    Acids_causal.p_loc = p.p_loc;
    Acids_causal.p_info = p.p_info;
  }

and annot_spec spec =
  let sd =
    match spec.s_desc with
    | Unspec ->
      Acids_causal.Unspec
    | Word pw ->
      let pw = Tree_word.map_upword annot_const_exp annot_const_exp pw in
      Acids_causal.Word pw
    | Interval (l, u) ->
      Acids_causal.Interval (annot_const_exp l, annot_const_exp u)
  in
  {
    Acids_causal.s_desc = sd;
    Acids_causal.s_loc = spec.s_loc;
  }

and annot_clock_annot cka =
  match cka with
  | Ca_var i ->
    Acids_causal.Ca_var i
  | Ca_on (cka, ce) ->
    Acids_causal.Ca_on (annot_clock_annot cka, annot_clock_exp ce)

and annot_dom dom =
  {
    Acids_causal.d_base_clock =
      Utils.map_opt annot_clock_annot dom.d_base_clock;
    Acids_causal.d_par = dom.d_par;
    Acids_causal.d_info = dom.d_info;
  }

and annot_buffer bu =
  {
    Acids_causal.bu_info = bu.bu_info;
  }

let annot_node_def nd =
  let body = annot_exp nd.n_body in
  check_causal nd.n_loc body;
  {
    Acids_causal.n_name = nd.n_name;
    Acids_causal.n_input = annot_pattern nd.n_input;
    Acids_causal.n_body = body;
    Acids_causal.n_pragma = nd.n_pragma;
    Acids_causal.n_const = nd.n_const;
    Acids_causal.n_loc = nd.n_loc;
    Acids_causal.n_info = nd.n_info;
  }

let annot_node_decl nd =
  {
    Acids_causal.decl_name = nd.decl_name;
    Acids_causal.decl_data = nd.decl_data;
    Acids_causal.decl_const = nd.decl_const;
    Acids_causal.decl_clock = nd.decl_clock;
    Acids_causal.decl_loc = nd.decl_loc;
  }

let annot_type_def td =
  {
    Acids_causal.ty_name = td.ty_name;
    Acids_causal.ty_body = td.ty_body;
    Acids_causal.ty_loc = td.ty_loc;
  }

let annot_const_def sd =
  {
    Acids_causal.sd_name = sd.sd_name;
    Acids_causal.sd_body = annot_exp sd.sd_body;
    Acids_causal.sd_loc = sd.sd_loc;
  }

let annot_pword_def pd =
  {
    Acids_causal.pd_name = pd.pd_name;
    Acids_causal.pd_body = annot_const_word pd.pd_body;
    Acids_causal.pd_loc = pd.pd_loc;
  }

let annot_type_phrase phr =
  match phr with
  | Phr_node_def nd ->
    Acids_causal.Phr_node_def (annot_node_def nd)
  | Phr_node_decl nd ->
    Acids_causal.Phr_node_decl (annot_node_decl nd)
  | Phr_type_def td ->
    Acids_causal.Phr_type_def (annot_type_def td)
  | Phr_const_def sd ->
    Acids_causal.Phr_const_def (annot_const_def sd)
  | Phr_pword_def pd ->
    Acids_causal.Phr_pword_def (annot_pword_def pd)

let annot_type_file file =
  {
    Acids_causal.f_name = file.f_name;
    Acids_causal.f_imports = file.f_imports;
    Acids_causal.f_info = file.f_info;
    Acids_causal.f_body = List.map annot_type_phrase file.f_body;
  }

(** {2 Putting it all together} *)

let file
    ctx
    (file
       :
       < interfaces : Interface.env; const_nodes : Acids_const.node_def list >
         Acids_clocked.file)
    =
  ctx, annot_type_file file

let pass =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_causal.print_file
       "causality"
       file)
