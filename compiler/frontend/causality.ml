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

(** {2 Errors} *)

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

(** {2 Environments} *)

type env =
  {
    ctx : Pass_manager.ctx;
    mutable idents : unit Union_find.point Ident.Env.t;
  }

let initial_env ctx =
  {
    ctx = ctx;
    idents = Ident.Env.empty;
  }

let fresh_class () = Union_find.fresh ()

(* TODO hack for dangling word variables *)
let find_var env v =
  try Ident.Env.find v env.idents
  with Not_found ->
    let ec = fresh_class () in
    env.idents <- Ident.Env.add v ec env.idents;
    ec

let add_var env v =
  let ec = fresh_class () in
  { env with idents = Ident.Env.add v ec env.idents; }

(** {2 Causality analysis} *)

open Acids_clocked

let union eqc1 eqc2 =
  if not (Union_find.equivalent eqc1 eqc2) then Union_find.union eqc1 eqc2

let rec enrich_env_with_pattern env p =
  match p.p_desc with
  | P_var v | P_condvar (v, _) ->
    add_var env v
  | P_tuple p_l ->
    List.fold_left enrich_env_with_pattern env p_l
  | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
    enrich_env_with_pattern env p
  | P_split pw ->
    Tree_word.fold_upword
      (fun p env -> enrich_env_with_pattern env p)
      (fun _ env -> env)
      pw
      env

let rec clock_exp env ce =
  match ce.ce_desc with
  | Ce_condvar v ->
    find_var env v
  | Ce_pword _ ->
    fresh_class ()
  | Ce_equal (ce, _) ->
    clock_exp env ce

let expect_clock_exp env eqc ce =
  let eqc' = clock_exp env ce in
  union eqc eqc'

let rec exp env e =
  match e.e_desc with
  | E_var v ->
    find_var env v
  | E_const _ ->
    fresh_class ()
  | E_fst e | E_snd e
  | E_app (_, e)
  | E_type_annot (e, _) | E_spec_annot (e, _) | E_clock_annot (e, _) ->
    exp env e
  | E_tuple e_l ->
    let ec = fresh_class () in
    List.iter (expect_exp env ec) e_l;
    ec
  | E_fby (e1, e2) ->
    let ec1 = exp env e1 in
    let ec2 = exp env e2 in
    if not (Clock_types.binary_clock_type e1.e_info#ei_clock)
    then union ec1 ec2;
    ec1
  | E_ifthenelse (e1, e2, e3) ->
    let ec = exp env e1 in
    expect_exp env ec e2;
    expect_exp env ec e3;
    ec
  | E_where (e, eqs) ->
    let env = block env eqs in
    exp env e
  | E_when (e, ce) | E_split (ce, e, _) ->
    let ec = exp env e in
    expect_clock_exp env ec ce;
    ec
  | E_bmerge (ce, e1, e2) ->
    let ec = clock_exp env ce in
    expect_exp env ec e1;
    expect_exp env ec e2;
    ec
  | E_merge (ce, c_l) ->
    let ec = clock_exp env ce in
    List.iter (fun c -> expect_exp env ec c.c_body) c_l;
    ec
  | E_valof ce ->
    clock_exp env ce
  | E_dom _ -> (* TODO *)
    assert false
  | E_buffer (e', bu) ->
    let ec = exp env e' in
    if bu.bu_info#bui_is_delay then fresh_class () else ec

and expect_exp env ec e =
  let ec' = exp env e in
  union ec ec'

and eq env eq =
  let ec = exp env eq.eq_rhs in
  expect_clock_type env ec eq.eq_rhs.e_info#ei_clock;
  ec

and clock_type env ty =
  let open Clock_types in
  match ty with
  | Ct_var _ -> fresh_class ()
  | Ct_stream st -> stream_type env st
  | Ct_prod ct_l ->
    let ec = fresh_class () in
    List.iter (expect_clock_type env ec) ct_l;
    ec

and expect_clock_type env ec ty =
  let ec' = clock_type env ty in
  union ec ec'

and stream_type env st =
  let open Clock_types in
  match st with
  | St_var _ -> fresh_class ()
  | St_on (st, ce) ->
    let ec = stream_type env st in
    expect_internal_clock_exp env ec ce;
    ec

and internal_clock_exp env ec =
  let open Clock_types in
  match ec with
  | Ce_condvar cev -> find_var env cev.cev_name
  | Ce_pword _ -> fresh_class ()
  | Ce_equal (ce, _) -> internal_clock_exp env ce

and expect_internal_clock_exp env ec ce =
  let ec' = internal_clock_exp env ce in
  union ec ec'

and block env eqs =
  let env =
    List.fold_left
      (fun env eq -> enrich_env_with_pattern env eq.eq_lhs)
      env
      eqs.b_body
  in

  let l = List.map (fun equ -> equ.eq_loc, equ.eq_lhs, eq env equ) eqs.b_body in

  let check (loc, p, rhs_ec) =
    let rec check p =
      match p.p_desc with
      | P_var v | P_condvar (v, _) ->
        let ec = find_var env v in
        if Union_find.equivalent ec rhs_ec then instantaneous_dep v loc
      | P_tuple p_l ->
        List.iter check p_l
      | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
        check p
      | P_split pw ->
        Tree_word.iter_upword check (fun _ -> ()) pw
    in
    check p
  in

  List.iter check l;

  env

let node_def env nd =
  let env = enrich_env_with_pattern env nd.n_input in
  ignore (exp env nd.n_body)

let phrase env phr =
  match phr with
  | Phr_node_def nd -> node_def env nd
  | Phr_node_decl _ | Phr_type_def _ -> ()

let file env file = List.iter (phrase env) file.f_body

(** {2 Putting it all together} *)

let check_file
    ctx
    (f
       :
       < interfaces : Interface.env; static_nodes : Acids_static.node_def list >
         Acids_clocked.file)
    =
  let env = initial_env ctx in
  file env f;
  ctx, f

let check =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_clocked.print_file
       "causality"
       check_file)
