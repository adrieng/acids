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
  let print_annot print fmt { new_annot = na; old_annot = oa; } =
    Format.fprintf fmt "new: %a, old: %a@."
      ANN.print_new_annot na
      print oa

  type clock_exp_info = A.I.clock_exp_info annot
  let print_clock_exp_info = print_annot A.I.print_clock_exp_info

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

  let annotate olda newa = { new_annot = newa; old_annot = olda; }
end

module type INFO_MAP =
sig
  module IN_INFO : Acids.S
  module OUT_INFO : Acids.S

  val update_clock_exp_info : IN_INFO.clock_exp_info -> OUT_INFO.clock_exp_info
  val update_exp_info : IN_INFO.exp_info -> OUT_INFO.exp_info
  val update_app_info : IN_INFO.app_info -> OUT_INFO.app_info
  val update_block_info : IN_INFO.block_info -> OUT_INFO.block_info
  val update_pat_info : IN_INFO.pat_info -> OUT_INFO.pat_info
  val update_eq_info : IN_INFO.eq_info -> OUT_INFO.eq_info
  val update_domain_info : IN_INFO.domain_info -> OUT_INFO.domain_info
  val update_node_info : IN_INFO.node_info -> OUT_INFO.node_info
end

module MakeMap
  (IN : Acids.A)
  (OUT : Acids.A with type I.var = IN.I.var)
  (M : INFO_MAP with module IN_INFO = IN.I and module OUT_INFO = OUT.I)
  =
struct
  open IN

  let rec extract_clock_exp ce =
    let ced =
      match ce.ce_desc with
      | Ce_var id -> OUT.Ce_var id
      | Ce_pword w ->
        let w = Ast_misc.map_upword extract_pword_exp extract_pword_exp w in
        OUT.Ce_pword w
      | Ce_equal (ce, e) ->
        OUT.Ce_equal (extract_clock_exp ce, extract_exp e)
      | Ce_iter ce ->
        OUT.Ce_iter (extract_clock_exp ce)
    in
    {
      OUT.ce_desc = ced;
      OUT.ce_loc = ce.ce_loc;
      OUT.ce_info = M.update_clock_exp_info ce.ce_info;
    }

  and extract_pword_exp pwe =
    match pwe with
    | Pwe_exp e -> OUT.Pwe_exp (extract_exp e)
    | Pwe_econstr ec -> OUT.Pwe_econstr ec
    | Pwe_fword i_l -> OUT.Pwe_fword i_l

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
      | E_dom (e, dom) ->
        OUT.E_dom (extract_exp e, extract_domain dom)
      | E_buffer e ->
        OUT.E_buffer (extract_exp e)
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
      | P_var (id, info) -> OUT.P_var (id, info)
      | P_tuple p_l -> OUT.P_tuple (List.map extract_pattern p_l)
      | P_clock_annot (p, ca) ->
        OUT.P_clock_annot (extract_pattern p, extract_clock_annot ca)
      | P_type_annot (p, ty) ->
        OUT.P_type_annot (extract_pattern p, ty)
      | P_split w ->
        OUT.P_split (Ast_misc.map_upword extract_pattern extract_exp w)
    in
    {
      OUT.p_desc = pd;
      OUT.p_loc = p.p_loc;
      OUT.p_info = M.update_pat_info p.p_info;
    }

  and extract_eq eq =
    {
      OUT.eq_lhs = extract_pattern eq.eq_lhs;
      OUT.eq_rhs = extract_exp eq.eq_rhs;
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
      OUT.decl_interv = nd.decl_interv;
      OUT.decl_clock = nd.decl_clock;
      OUT.decl_loc = nd.decl_loc;
    }

  and extract_type_def td =
    {
      OUT.ty_name = td.ty_name;
      OUT.ty_body = td.ty_body;
      OUT.ty_loc = td.ty_loc;
    }

  let extract_phrase phr =
    match phr with
    | Phr_node_def nd -> OUT.Phr_node_def (extract_node_def nd)
    | Phr_node_decl nd -> OUT.Phr_node_decl (extract_node_decl nd)
    | Phr_type_def td -> OUT.Phr_type_def (extract_type_def td)

  let extract_file f =
    {
      OUT.f_name = f.f_name;
      OUT.f_imports = f.f_imports;
      OUT.f_info = f.f_info;
      OUT.f_body = List.map extract_phrase f.f_body;
    }
end
