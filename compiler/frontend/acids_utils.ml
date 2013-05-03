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

module type S =
sig
  module A : Acids.S
  module B : Acids.S with type var = A.var

  type new_annot
  val print_new_annot : Format.formatter -> new_annot -> unit

  val update_clock_exp_info : A.clock_exp_info -> new_annot -> B.clock_exp_info
  val update_exp_info : A.exp_info -> new_annot -> B.exp_info
  val update_app_info : A.app_info -> new_annot -> B.app_info
  val update_block_info : A.block_info -> new_annot -> B.block_info
  val update_pat_info : A.pat_info -> new_annot -> B.pat_info
  val update_eq_info : A.eq_info -> new_annot -> B.eq_info
  val update_node_info : A.node_info -> new_annot -> B.node_info
end

module MakeAnnot = functor (S : S) ->
struct
  module Info =
  struct
    type var = S.A.var
    let print_var = S.A.print_var

    type 'a annot = { new_annot : S.new_annot; old_annot : 'a; }
    let print_annot print fmt { new_annot = na; old_annot = oa; } =
      Format.fprintf fmt "new: %a, old: %a@."
        S.print_new_annot na
        print oa

    type clock_exp_info = S.A.clock_exp_info annot
    let print_clock_exp_info = print_annot S.A.print_clock_exp_info

    type exp_info = S.A.exp_info annot
    let print_exp_info = print_annot S.A.print_exp_info

    type app_info = S.A.app_info annot
    let print_app_info = print_annot S.A.print_app_info

    type block_info = S.A.block_info annot
    let print_block_info = print_annot S.A.print_block_info

    type pat_info = S.A.pat_info annot
    let print_pat_info = print_annot S.A.print_pat_info

    type eq_info = S.A.eq_info annot
    let print_eq_info = print_annot S.A.print_eq_info

    type node_info = S.A.node_info annot
    let print_node_info = print_annot S.A.print_node_info
  end

  module Mannot = Acids.Make(Info)
  module M = Acids.Make(S.B)

  let annotate old newa =
    let open Info in
    { new_annot = newa; old_annot = old; }

  (** {2 Maps to new information} *)

  let update update_annot annot =
    let open Info in
    update_annot annot.old_annot annot.new_annot

  include Mannot

  let rec extract_clock_exp ce =
    let ced =
      match ce.ce_desc with
      | Ce_var id -> M.Ce_var id
      | Ce_pword w ->
        M.Ce_pword (Ast_misc.map_upword extract_exp extract_exp w)
      | Ce_equal (ce, e) ->
        M.Ce_equal (extract_clock_exp ce, extract_exp e)
      | Ce_iter ce ->
        M.Ce_iter (extract_clock_exp ce)
    in
    {
      M.ce_desc = ced;
      M.ce_loc = ce.ce_loc;
      M.ce_info = update S.update_clock_exp_info ce.ce_info;
    }

  and extract_exp e =
    let ed =
      match e.e_desc with
      | E_var id -> M.E_var id
      | E_const c -> M.E_const c
      | E_fst e -> M.E_fst (extract_exp e)
      | E_snd e -> M.E_snd (extract_exp e)
      | E_tuple e_l -> M.E_tuple (List.map extract_exp e_l)
      | E_fby (e1, e2) -> M.E_fby (extract_exp e1, extract_exp e2)
      | E_ifthenelse (e1, e2, e3) ->
        M.E_ifthenelse (extract_exp e1, extract_exp e2, extract_exp e3)
      | E_app (app, e) -> M.E_app (extract_app app, extract_exp e)
      | E_where (e, block) -> M.E_where (extract_exp e, extract_block block)
      | E_when (e, ce) -> M.E_when (extract_exp e, extract_clock_exp ce)
      | E_split (ce, e, ec_l) ->
        M.E_split (extract_clock_exp ce, extract_exp e, ec_l)
      | E_bmerge (ce, e1, e2) ->
        M.E_bmerge (extract_clock_exp ce, extract_exp e1, extract_exp e2)
      | E_merge (ce, c_l) ->
        M.E_merge (extract_clock_exp ce, List.map extract_merge_clause c_l)
      | E_valof ce ->
        M.E_valof (extract_clock_exp ce)
      | E_clockannot (e, ca) ->
        M.E_clockannot (extract_exp e, extract_clock_annot ca)
      | E_dom (e, dom) ->
        M.E_dom (extract_exp e, extract_domain dom)
    in
    {
      M.e_desc = ed;
      M.e_loc = e.e_loc;
      M.e_info = update S.update_exp_info e.e_info;
    }

  and extract_app app =
    {
      M.a_op = app.a_op;
      M.a_loc = app.a_loc;
      M.a_info = update S.update_app_info app.a_info;
    }

  and extract_block block =
    {
      M.b_body = List.map extract_eq block.b_body;
      M.b_loc = block.b_loc;
      M.b_info = update S.update_block_info block.b_info;
    }

  and extract_pattern p =
    let pd =
      match p.p_desc with
      | P_var id -> M.P_var id
      | P_tuple p_l -> M.P_tuple (List.map extract_pattern p_l)
      | P_clock_annot (p, ca) ->
        M.P_clock_annot (extract_pattern p, extract_clock_annot ca)
      | P_split w ->
        M.P_split (Ast_misc.map_upword extract_pattern extract_exp w)
    in
    {
      M.p_desc = pd;
      M.p_loc = p.p_loc;
      M.p_info = update S.update_pat_info p.p_info;
    }

  and extract_eq eq =
    {
      M.eq_lhs = extract_pattern eq.eq_lhs;
      M.eq_rhs = extract_exp eq.eq_rhs;
      M.eq_loc = eq.eq_loc;
      M.eq_info = update S.update_eq_info eq.eq_info;
    }

  and extract_merge_clause c =
    {
      M.c_sel = c.c_sel;
      M.c_body = extract_exp c.c_body;
      M.c_loc = c.c_loc;
    }

  and extract_clock_annot ca =
    match ca with
    | Ca_var i -> M.Ca_var i
    | Ca_on (ca, ce) -> M.Ca_on (extract_clock_annot ca, extract_clock_exp ce)

  and extract_domain dom =
    {
      M.d_base_clock = Utils.map_opt extract_clock_annot dom.d_base_clock;
      M.d_par = dom.d_par;
    }

  and extract_node_def nd =
    {
      M.n_name = nd.n_name;
      M.n_input = extract_pattern nd.n_input;
      M.n_body = extract_exp nd.n_body;
      M.n_pragma = nd.n_pragma;
      M.n_static = nd.n_static;
      M.n_loc = nd.n_loc;
      M.n_info = update S.update_node_info nd.n_info;
    }

  and extract_node_decl nd =
    {
      M.decl_name = nd.decl_name;
      M.decl_data = nd.decl_data;
      M.decl_static = nd.decl_static;
      M.decl_interv = nd.decl_interv;
      M.decl_clock = nd.decl_clock;
      M.decl_loc = nd.decl_loc;
    }

  and extract_type_def td =
    {
      M.ty_name = td.ty_name;
      M.ty_body = td.ty_body;
      M.ty_loc = td.ty_loc;
    }

  let extract_phrase phr =
    match phr with
    | Phr_node_def nd -> M.Phr_node_def (extract_node_def nd)
    | Phr_node_decl nd -> M.Phr_node_decl (extract_node_decl nd)
    | Phr_type_def td -> M.Phr_type_def (extract_type_def td)

  let extract_file f =
    {
      M.f_name = f.f_name;
      M.f_imports = f.f_imports;
      M.f_info = f.f_info;
      M.f_body = List.map extract_phrase f.f_body;
    }
end
