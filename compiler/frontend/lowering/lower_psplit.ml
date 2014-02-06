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

(** {1 Remove split patterns from the language}

        (<x^2 (y^4 z^5)>, k) = e

    ->
        (ps, k) = e
    and (x, y, z) = split ps by 0^2 (1^4 2^5) with 0, 1, 2
*)

module SUB = Acids_utils.MAP_SUB(Acids_causal)

open Acids_causal
open Acids_causal_utils

let psplit_var_prefix = "pspl"

(** {2 Handling patterns} *)

let translate_psplit st ps =
  let add p (i, p_l) =
    make_const_exp_int st i, (Int.succ i, p :: p_l)
  in

  let pw, (sup, p_l) =
    Tree_word.mapfold_upword
      add
      (fun i acc -> i, acc)
      ps
      (Int.zero, [])
  in

  pw, sup, p_l

let make_eq_split ty st v p_l sup pw =
  (* p_l = split v by pw with 0, ..., sup - 1 *)

  let e =
    let e_v = make_exp_st ty st (E_var v) in

    let ec_l =
      (* Build selectors reversed since pw should be too *)
      let rec add ec_l i =
        if Int.(i >= sup)
        then ec_l
        else add (Ast_misc.Ec_int i :: ec_l) (Int.succ i)
      in
      add [] Int.zero
    in

    let ce = make_clock_exp_pword st pw in
    make_exp_st ty st (E_split (ce, e_v, ec_l))
  in

  let p = make_pat ty (Clock_types.Ct_stream st) (P_tuple p_l) in

  make_plain_eq p e

let rec remove_psplit_in_pat p current_eqs =
  let pd, current_eqs =
    match p.p_desc with
    | P_var _ ->
      p.p_desc, current_eqs
    | P_tuple p_l ->
      let p_l, current_eqs =
        Utils.mapfold remove_psplit_in_pat p_l current_eqs
      in
      P_tuple p_l, current_eqs
    | P_clock_annot (p, a) ->
      let p, current_eqs = remove_psplit_in_pat p current_eqs in
      P_clock_annot (p, a), current_eqs
    | P_type_annot (p, a) ->
      let p, current_eqs = remove_psplit_in_pat p current_eqs in
      P_type_annot (p, a), current_eqs
    | P_spec_annot (p, a) ->
      let p, current_eqs = remove_psplit_in_pat p current_eqs in
      P_spec_annot (p, a), current_eqs
    | P_split ps ->
      let ps, current_eqs =
        Tree_word.mapfold_upword
          remove_psplit_in_pat
          (fun se current_eqs -> se, current_eqs)
          ps
          current_eqs
      in

      let base_st = Clock_types.get_st p.p_info#pi_clock in
      let pw, sup, p_l = translate_psplit base_st ps in
      let id = Ident.make_internal psplit_var_prefix in
      let eq = make_eq_split p.p_info#pi_data base_st id p_l sup pw in
      P_var id, eq :: current_eqs
  in
  { p with p_desc = pd; }, current_eqs

let remove_psplit_eq current_eqs eq =
  let current_eqs, eqd =
    match eq.eq_desc with
    | Eq_plain (p, e) ->
      let p, current_eqs = remove_psplit_in_pat p current_eqs in
      current_eqs, Eq_plain (p, e)
    | Eq_condvar _ ->
      current_eqs, eq.eq_desc
  in
  current_eqs, { eq with eq_desc = eqd; }

let remove_psplit_block block =
  let current_eqs, body = Utils.mapfold_left remove_psplit_eq [] block.b_body in
  { block with b_body = current_eqs @ body; }

let rec remove_psplit_exp e =
  let e =
    match e.e_desc with
    | E_where (e, block) ->
      let block = remove_psplit_block block in
      { e with e_desc = E_where (e, block); }
    | _ ->
      e
  in
  SUB.map_sub_exp remove_psplit_exp e

let node_def input body =
  let input, eqs = remove_psplit_in_pat input [] in
  input, remove_psplit_exp (add_eqs_to_exp eqs body)

(** {2 Putting it all together} *)

let pass = Lowering_utils.make_transform_by_node node_def "lower_psplit"
