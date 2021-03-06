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

open Acids_causal

(* Useful definition *)
type annotated_file =
  < interfaces : Interface.env;
    const_nodes : Acids_const.node_def list; > file

module T = Acids_utils.TRANSLATE_CLOCK_EXP(Acids_causal)

let trans_clock_exp find_pword ce =
  let find_bounds info = info#ci_bounds in
  let find_specs info = info#ci_specs in
  T.trans_clock_exp find_pword find_bounds find_specs ce

let make_const_exp ?(loc = Loc.dummy) ty st desc =
  {
    se_desc = desc;
    se_info =
      object
        method pwi_data = ty
        method pwi_clock = st
      end;
    se_loc = loc;
  }

let make_const_exp_bool ?(loc = Loc.dummy) st b =
  make_const_exp ~loc Data_types.Tys_bool st (Ast_misc.Ec_bool b)

let make_const_exp_int ?(loc = Loc.dummy) st i =
  make_const_exp ~loc Data_types.Tys_int st (Ast_misc.Ec_int i)

let make_clock_exp ?(loc = Loc.dummy) ty st bounds specs desc =
  {
    ce_desc = desc;
    ce_info =
      object
        method ci_data = ty
        method ci_clock = st
        method ci_bounds = bounds
        method ci_specs = specs
      end;
    ce_loc = loc;
  }

let make_clock_exp_bool ?(loc = Loc.dummy) st desc =
  make_clock_exp
    ~loc
    Data_types.Tys_bool
    st
    Interval.bool
    [Ast_misc.Interval Interval.bool]
    desc

let make_clock_exp_not ?(loc = Loc.dummy) ce =
  assert (ce.ce_info#ci_data = Data_types.Tys_bool);
  let base_st = ce.ce_info#ci_clock in
  make_clock_exp_bool
    ~loc
    base_st
    (Ce_equal (ce, make_const_exp_bool base_st false))

let make_clock_exp_pword ?(loc = Loc.dummy) st pw =
  let get se = Ast_misc.int_of_econstr se.se_desc in
  let p = Tree_word.map_upword get get pw in
  let l, u = Ast_misc.bounds_of_int_pword p in
  let it = Interval.make l u in
  make_clock_exp
    ~loc
    Data_types.Tys_int
    st
    it
    Ast_misc.([Interval it; Word p])
    (Ce_pword (Pd_lit pw))

let make_exp ?(loc = Loc.dummy) ?(relevant_deps = true) ty ct desc =
  {
    e_desc = desc;
    e_info =
      object
        method ei_data = ty
        method ei_clock = ct
        method ei_relevant_deps = relevant_deps
      end;
    e_loc = loc;
  }

let make_exp_st ?(loc = Loc.dummy) ?(relevant_deps = true) ty st desc =
  make_exp ~loc ~relevant_deps ty (Clock_types.Ct_stream st) desc

let make_sampled_exp find_pword e ce =
  let clock_ce = trans_clock_exp find_pword ce in
  let base_st = Clock_types.get_st e.e_info#ei_clock in
  make_exp_st
    e.e_info#ei_data
    (Clock_types.St_on (base_st, clock_ce))
    (E_when (e, ce))

let make_pat ty ct pd =
  {
    p_desc = pd;
    p_loc = Loc.dummy;
    p_info =
      object
        method pi_data = ty
        method pi_clock = ct
      end;
  }

let make_plain_eq ?(loc = Loc.dummy) p e =
  {
    eq_desc = Eq_plain (p, e);
    eq_loc = loc;
    eq_info = ();
  }

let make_block eqs =
  {
    b_body = eqs;
    b_loc = Loc.dummy;
    b_info = ();
  }

let add_eqs_to_exp eqs e =
  match eqs with
  | [] -> e
  | _ :: _ ->
    let e', block =
      match e.e_desc with
      | E_where (e', block) -> e', { block with b_body = eqs @ block.b_body; }
      | _ -> e, make_block eqs
    in
    { e with e_desc = E_where (e', block); }

let apply_to_node_defs f_node file =
  let lower_node nd =
    Ident.set_current_ctx nd.n_info#ni_ctx;
    let input, body = f_node nd.n_input nd.n_body in
    { nd with n_input = input; n_body = body; }
  in

  let lower_phrase phr =
    match phr with
    | Phr_node_def nd ->
      Phr_node_def (lower_node nd)
    | Phr_node_decl _ | Phr_type_def _ | Phr_const_def _ | Phr_pword_def _ ->
      phr
  in

  { file with f_body = List.map lower_phrase file.f_body; }
