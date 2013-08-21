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

(** {1 Lower nested local declarations}

    This pass ensures that there are only two places where local definitions can
    be present: either at top-level in a node body, or immediately below
    a domain.

    This should come after code has been put into three-address form.
*)

open Acids_causal
open Acids_causal_utils

module SUB = Acids_utils.MAP_SUB(Acids_causal)

let rec lower_where (eqs : eq list) e =
  match e.e_desc with
  | E_where (e, block) ->
    lower_where_block eqs block, e

  | E_dom (e', dom) ->
    eqs, { e with e_desc = E_dom (close_exp e', dom); }

  | _ ->
    eqs, e

and lower_where_eq eqs eq =
  let eqs, eqd =
    match eq.eq_desc with
    | Eq_plain (p, e) ->
      let eqs, e = lower_where eqs e in
      eqs, Eq_plain (p, e)
    | Eq_condvar (v, specs, e) ->
      let eqs, e = lower_where eqs e in
      eqs, Eq_condvar (v, specs, e)
  in
  { eq with eq_desc = eqd; } :: eqs

and lower_where_block eqs block =
  List.fold_left lower_where_eq eqs block.b_body

and close_exp e =
  let eqs, e = lower_where [] e in
  add_eqs_to_exp eqs e

let lower_where_node input body = input, close_exp body

(** {2 Putting it all together} *)

let pass = Lowering_utils.make_transform_by_node lower_where_node "lower_where"
