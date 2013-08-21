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

(** {1 Remove sub-expressions from the language}

    This pass puts Acids_causal into a form of so-called "three-address code".
    It means that all sub-expressions are variables.

    E.g.:

    x = 0 fby (y + 1)

    becomes

    s0 = 0
    s1 = 1
    s2 = y + s1
    x = s0 fby s2

    Note that we do not move sub-expressions from inside a block (E_where) above
    it, since we do not want to create scope extrusion problems. Same for
    domains.

    We also ensure that after translation, in an expression "e where rec block",
    e is a variable.
*)

open Acids_causal
open Acids_causal_utils

let var_prefix = "s"

(** {2 Walking the AST} *)

(* TODO rename functions *)

let rec lower_sub_exp (current_eqs : eq list) e =
  let current_eqs, ed =
    match e.e_desc with
    | E_var _ | E_const _ | E_valof _ ->
      current_eqs, e.e_desc

    | E_dom (e, dom) ->
      current_eqs, E_dom (close_exp e, dom)

    | E_where (e, block) ->
      let current_eqs = lower_block current_eqs block in
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, e.e_desc

    (* The remaining are boring cases *)

    | E_fst e ->
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, E_fst e

    | E_snd e ->
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, E_snd e

    | E_tuple e_l ->
      let e_l, current_eqs =
        Utils.mapfold (Utils.double_flip lower_exp) e_l current_eqs
      in
      current_eqs, E_tuple e_l

    | E_fby (e1, e2) ->
      let current_eqs, e1 = lower_exp current_eqs e1 in
      let current_eqs, e2 = lower_exp current_eqs e2 in
      current_eqs, E_fby (e1, e2)

    | E_ifthenelse (e1, e2, e3) ->
      let current_eqs, e1 = lower_exp current_eqs e1 in
      let current_eqs, e2 = lower_exp current_eqs e2 in
      let current_eqs, e3 = lower_exp current_eqs e3 in
      current_eqs, E_ifthenelse (e1, e2, e3)

    | E_app (app, e) ->
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, E_app (app, e)

    | E_when (e, ce) ->
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, E_when (e, ce)

    | E_split (ce, e, ec_l) ->
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, E_split (ce, e, ec_l)

    | E_bmerge (ce, e1, e2) ->
      let current_eqs, e1 = lower_exp current_eqs e1 in
      let current_eqs, e2 = lower_exp current_eqs e2 in
      current_eqs, E_bmerge (ce, e1, e2)

    | E_merge (ce, c_l) ->
      let lower_clause current_eqs c =
        let current_eqs, body = lower_exp current_eqs c.c_body in
        current_eqs, { c with c_body = body; }
      in
      let current_eqs, c_l = Utils.mapfold_left lower_clause current_eqs c_l in
      current_eqs, E_merge (ce, c_l)

    | E_clock_annot (e, a) ->
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, E_clock_annot (e, a)

    | E_type_annot (e, a) ->
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, E_type_annot (e, a)

    | E_spec_annot (e, a) ->
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, E_spec_annot (e, a)

    | E_buffer (e, bu) ->
      let current_eqs, e = lower_exp current_eqs e in
      current_eqs, E_buffer (e, bu)
  in
  current_eqs, { e with e_desc = ed; }

and lower_exp current_eqs e =
  match e.e_desc with
  | E_var _ -> current_eqs, e
  | _ ->
    let current_eqs, e = lower_sub_exp current_eqs e in
    let cnd = Ident.make_internal var_prefix in
    let eq =
      make_plain_eq
        (make_pat e.e_info#ei_data e.e_info#ei_clock (P_var cnd))
        e
    in
    eq :: current_eqs, { e with e_desc = E_var cnd; }

and lower_block block =
  let current_eqs, body =
    Utils.mapfold_left lower_eq [] block.b_body
  in
  { block with b_body = current_eqs @ body; }

and lower_eq current_eqs eq =
  let current_eqs, eqd =
    match eq.eq_desc with
    | Eq_plain (p, e) ->
      let current_eqs, e = lower_sub_exp current_eqs e in
      current_eqs, Eq_plain (p, e)
    | Eq_condvar (v, specs, e) ->
      let current_eqs, e = lower_sub_exp current_eqs e in
      current_eqs, Eq_condvar (v, specs, e)
  in
  current_eqs, { eq with eq_desc = eqd; }

and close_exp e =
  let current_eqs, e = lower_exp [] e in
  add_eqs_to_exp current_eqs e

let node_def input body = input, close_exp body

(** {2 Putting it all together} *)

let pass = Lowering_utils.make_transform_by_node node_def "lower_subexps"
