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

(** {1 Remove high-level constructs from the language}

    This pass removes the following constructs from Acids_causal:

    FBY:

    - [| e1 fby e2 |] =
      merge true(false) (e1 when true(false)) (buffer e2)

    IF:

    - [| if valof ce then e2 else e3 |] =
      merge ce (e2 when ce) (e3 when (ce = false))

    - [| if e1 then e2 else e3 |] =
      merge (valof c) (e2 when c) (e3 when (c = false)) where rec cond c = e1
*)

open Acids_causal
open Acids_causal_utils

let if_var_prefix = "if_cnd"

(** {2 Translations} *)

(*
  e1 fby e2
  ->
  merge true(false) (e1 when true(false)) (buffer e2)

*)
let fby_translation find_pword e1 e2 =
  let base_st = Clock_types.get_st e1.e_info#ei_clock in

  let pw =
    let open Tree_word in
    {
      u = Leaf true;
      v = Leaf false;
    }
  in

  let pw_se =
    Tree_word.map_upword
      (make_const_exp_bool base_st)
      (make_const_exp_int base_st)
      pw
  in

  let cond_ce =
    make_clock_exp_bool
      base_st
      (Ce_pword (Pd_lit pw_se))
  in

  let clock_ce =
    let mk b = Ast_misc.Ec_bool b in
    Clock_types.Ce_pword (Tree_word.map_upword mk (fun x -> x) pw)
  in

  (* e1 when ce *)
  let e1' = make_sampled_exp find_pword e1 cond_ce in

  (* buffer e2 *)
  let e2' =
    let bu =
      {
        bu_info =
          object
            method bui_is_delay = not e2.e_info#ei_relevant_deps
            method bui_size = Int.one
          end;
      }
    in

    make_exp_st
      e2.e_info#ei_data
      Clock_types.(St_on (base_st, Ce_equal (clock_ce, Ast_misc.Ec_bool false)))
      (E_buffer (e2, bu))
  in

  make_exp_st e1.e_info#ei_data base_st (E_bmerge (cond_ce, e1', e2'))

(*
  if valof ce then e1 else e2
  ->
  merge ce (e1 when ce) (e2 when (ce = false))
*)

let merge_valof_translation find_pword ce e1 e2 =
  make_exp_st
    e1.e_info#ei_data
    ce.ce_info#ci_clock
    (E_bmerge (ce,
               make_sampled_exp find_pword e1 ce,
               make_sampled_exp find_pword e2 (make_clock_exp_not ce)))

(*
  if e1 then e2 else e3
  ->
  [| merge valof if_cnd e2 e3 |] where rec if_cnd = e1

  with if_cnd a fresh identifier
*)

let merge_translation find_pword e1 e2 e3 =
  let cnd = Ident.make_internal if_var_prefix in

  let base_st = Clock_types.get_st e1.e_info#ei_clock in

  let block =
    let eq =
      make_plain_eq
        (make_pat e1.e_info#ei_data e1.e_info#ei_clock (P_var cnd))
        e1
    in
    make_block [eq]
  in

  let e_merge =
    let ce =
      make_clock_exp_bool
        base_st
        (Ce_condvar cnd)
    in
    merge_valof_translation find_pword ce e2 e3
  in

  make_exp_st e2.e_info#ei_data base_st (E_where (e_merge, block))

(** {2 Environment} *)

type env =
  {
    intf_env : Interface.env;
    local_pwords : Ast_misc.const_pword Names.ShortEnv.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    local_pwords = Names.ShortEnv.empty;
  }

let add_pword env pn pw =
  let get se = se.se_desc in
  let get_int se = Ast_misc.get_int (get se) in
  let local_pwords =
    Names.ShortEnv.add pn (Tree_word.map_upword get get_int pw) env.local_pwords
  in
  { env with local_pwords = local_pwords; }

let find_pword env ln =
  let open Names in
  match ln.modn with
  | LocalModule ->
    ShortEnv.find ln.shortn env.local_pwords
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    Interface.((find_pword intf ln.shortn).pi_value)

(** {2 Walking the AST} *)

let rec lower_exp env e =
  let lower_exp = lower_exp env in
  let find_pword = find_pword env in

  let ed =
    match e.e_desc with
    | E_var _ | E_const _ | E_valof _ ->
      e.e_desc

    | E_fst e ->
      E_fst (lower_exp e)

    | E_snd e ->
      E_snd (lower_exp e)

    | E_tuple e_l ->
      E_tuple (List.map lower_exp e_l)

    | E_fby (e1, e2) ->
      (fby_translation find_pword (lower_exp e1) (lower_exp e2)).e_desc

    | E_ifthenelse (e1, e2, e3) ->
      let e =
        (
          match e1.e_desc with
          | E_valof ce -> merge_valof_translation find_pword ce e2 e3
          | _ -> merge_translation find_pword e1 e2 e3
        )
      in
      e.e_desc

    | E_app (app, e) ->
      E_app (app, lower_exp e)

    | E_where (e, block) ->
      E_where (lower_exp e, lower_block env block)

    | E_when (e, ce) ->
      E_when (lower_exp e, ce)

    | E_split (ce, e, ec_l) ->
      E_split (ce, lower_exp e, ec_l)

    | E_bmerge (ce, e1, e2) ->
      E_bmerge (ce, lower_exp e1, lower_exp e2)

    | E_merge (ce, c_l) ->
      let lower_clause c = { c with c_body = lower_exp c.c_body; } in
      E_merge (ce, List.map lower_clause c_l)

    | E_clock_annot (e, cka) ->
      E_clock_annot (lower_exp e, cka)

    | E_type_annot (e, tya) ->
      E_type_annot (lower_exp e, tya)

    | E_spec_annot (e, spec) ->
      E_spec_annot (lower_exp e, spec)

    | E_dom (e, dom) ->
      E_dom (lower_exp e, dom)

    | E_buffer (e, bu) ->
      E_buffer (lower_exp e, bu)
  in
  { e with e_desc = ed; }

and lower_block env block =
  { block with b_body = List.map (lower_eq env) block.b_body; }

and lower_eq env eq =
  let eqd =
    match eq.eq_desc with
    | Eq_plain (p, e) -> Eq_plain (p, lower_exp env e)
    | Eq_condvar (v, specs, e) -> Eq_condvar (v, specs, lower_exp env e)
  in
  { eq with eq_desc = eqd; }

let lower_node env nd =
  Ident.set_current_ctx nd.n_info#ni_ctx;
  { nd with n_body = lower_exp env nd.n_body; }

let lower_phrase env phr =
  match phr with
  | Phr_node_def nd -> env, Phr_node_def (lower_node env nd)
  | Phr_node_decl _ | Phr_type_def _ | Phr_const_def _ -> env, phr
  | Phr_pword_def pd -> add_pword env pd.pd_name pd.pd_body, phr

(** {2 Putting it all together} *)

let pass =
  let tr file =
    let env = initial_env file.f_info#interfaces in
    let _, body = Utils.mapfold_left lower_phrase env file.f_body in
    { file with f_body = body; }
  in
  Lowering_utils.make_transform_by_file tr "lower_constructs"
