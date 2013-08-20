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

(** {1 Remove tuple from the language}

    This pass assumes that the input is in three-addess form and have no
    if/then/else, fbys or split patterns, and thus must come after
    Lower_constructs, Lower_psplit and Lower_subexps.

    It works in two phases:

    1/ Eliminate variables of product type, and product type annotations.
    TODO and move clock type annotations to variables

    x = (1, 2)
    y = 4
    z = (y, x) when ce

    gets translated to

    (x1, x2) = (1, 2)
    y = 4
    (z1, (z2, z3)) = (y, (x1, x2)) when ce

    2/ Remove projections

    3/ Simplify equations with tuple patterns on the left.

    (x1, x2) = (1, 2)
    y = 4
    ((z1, z2), z3) = (y, (x1, x2)) when ce

    gets translated to

    x1 = 1
    x2 = 2
    y = 4
    z1 = y when ce
    z2 = x1 when ce
    z3 = x2 when ce
*)

module SUB = Acids_utils.MAP_SUB(Acids_causal)
module SUBST = Acids_utils.SUBST(Acids_causal)

open Acids_causal
open Acids_causal_utils

let prod_var_prefix = "t"

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    prod_var_env : exp Ident.Env.t;
    (** maps variable of product type to tuple exps *)
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    prod_var_env = Ident.Env.empty;
  }

let add_var env v e =
  (* update the existing environment itself *)
  let prod_var_env =
    let subst = Ident.Env.add v e Ident.Env.empty in
    Ident.Env.map (SUBST.subst_exp subst) env.prod_var_env
  in
  { env with prod_var_env = Ident.Env.add v e prod_var_env; }

(** {2 Eliminate tuple variables} *)

let rec make_scalar_pat_exp ty ct =
  let open Data_types in
  let open Clock_types in
  match ty, ct with
  | (Ty_var _ | Ty_scal _ | Ty_cond _), _ ->
    let v = Ident.make_internal prod_var_prefix in
    make_exp ty ct (E_var v), make_pat ty ct (P_var v)
  | Ty_prod ty_l, Ct_prod ct_l ->
    let ep_l = List.map2 make_scalar_pat_exp ty_l ct_l in
    let e_l, p_l = List.split ep_l in
    make_exp ty ct (E_tuple e_l), make_pat ty ct (P_tuple p_l)
  | Ty_prod ty_l, (Ct_var _ | Ct_stream _) ->
    let ep_l = List.map (fun ty -> make_scalar_pat_exp ty ct) ty_l in
    let e_l, p_l = List.split ep_l in
    make_exp ty ct (E_tuple e_l), make_pat ty ct (P_tuple p_l)

let rec decompose_tuple_pat p env =
  let open Data_types in
  match p.p_desc with
  | P_var v ->
    (
      match p.p_info#pi_data with
      | Ty_prod _ ->
        let e, p = make_scalar_pat_exp p.p_info#pi_data p.p_info#pi_clock in
        p, add_var env v e
      | Ty_var _ | Ty_scal _ | Ty_cond _ ->
        p, env
    )
  | P_tuple p_l ->
    let p_l, env = Utils.mapfold decompose_tuple_pat p_l env in
    { p with p_desc = P_tuple p_l; }, env
  | P_clock_annot (p, cka) ->
    let p, env = decompose_tuple_pat p env in
    { p with p_desc = P_clock_annot (p, cka) ; }, env
  | P_type_annot (p, Ty_prod ty_l) ->
    (
      let p, env = decompose_tuple_pat p env in
      match p.p_desc with
      | P_tuple p_l ->
        let p_l =
          let retag p ty = { p with p_desc = P_type_annot (p, ty); } in
          List.map2 retag p_l ty_l
        in
        { p with p_desc = P_tuple p_l; }, env
      | _ ->
        assert false
    )
  | P_type_annot (p, ((Ty_var _ | Ty_scal _ | Ty_cond _) as tya)) ->
    let p, env = decompose_tuple_pat p env in
    { p with p_desc = P_type_annot (p, tya) ; }, env
  | P_spec_annot (p, spec) ->
    let p, env = decompose_tuple_pat p env in
    { p with p_desc = P_spec_annot (p, spec) ; }, env
  | P_split pw ->
    let pw, env =
      Tree_word.mapfold_upword
        decompose_tuple_pat
        (fun i env -> i, env)
        pw
        env
    in
    { p with p_desc = P_split pw; }, env

let decompose_tuple_eq env eq =
  let eqd, env =
    match eq.eq_desc with
    | Eq_plain (p, e) ->
      let p, env = decompose_tuple_pat p env in
      Eq_plain (p, e), env
    | Eq_condvar _ ->
      eq.eq_desc, env
  in
  env, { eq with eq_desc = eqd; }

let decompose_tuple_block env block =
  (* First compute substitution and update patterns...  *)
  let env, body = Utils.mapfold_left decompose_tuple_eq env block.b_body in
  (* Then apply substitution to the body *)
  let body = List.map (SUBST.subst_eq env.prod_var_env) body in
  env, { block with b_body = body; }

let rec decompose_tuple_exp env e =
  let e =
    match e.e_desc with
    | E_where (e', block) ->
      let env, block = decompose_tuple_block env block in
      let e' = SUBST.subst_exp env.prod_var_env e' in
      { e with e_desc = E_where (e', block); }
    | _ ->
      e
  in
  SUB.map_sub_exp (decompose_tuple_exp env) e

(** {2 Remove projections} *)

let rec remove_proj_exp e =
  let e =
    match e.e_desc with
    | E_fst { e_desc = E_tuple [e1; _]; } ->
      e1
    | E_snd { e_desc = E_tuple [_; e2]; } ->
      e2
    | _ ->
      e
  in
  SUB.map_sub_exp remove_proj_exp e

(** {2 Simplify equations} *)

(*
  Simplification rules:

  - projections have been eliminated above

  - tuples generate sub-equations:
  (x1, x2) = (1, 2) -> x1 = 1 and x2 = 2

  - (fby and if/then/else have been eliminated earlier)

  - applications: do nothing, since our final target is an n-ary language

  - where: nothing special

  - when: flatten
  (x1, x2) = (z1, z2) when ce -> x1 = z1 when c1 and x2 = z2 when c2

  - split:
  ((y1, y2), (z1, z2)) = split (x1, x2) with ce by ec_l ->
  (y1, z1) = split x1 with ce by ec_l
  and (y2, z2) = split x2 with ce by ec_l

  - merge and bmerge: flatten
  (x1, x2) = merge ce (y1, y2) (z1, z2) ->
  x1 = merge ce y1 z1
  and x2 = merge ce y2 z2

  - valof: do nothing

  - clock annot: flatten
  (x1, x2) = (y1, y2) :: 'a on ce
  ->
  x1 = y1 :: 'a on ce
  x2 = y2 :: 'a on ce

  - type annot: flatten, including the annotation
  (x1, x2) = (y1, y2) :: (ty1, ty2)
  ->
  x1 = y1 :: ty1
  x2 = y2 :: ty2

  - spec annot: do nothing, since specs force their argument to be of scalar
  type.

  - dom: nothing special

  - buffer: flatten
  (x1, x2) = buffer (y1, y2) -> x1 = buffer x2 and y1 = buffer y2
*)

let not_prod ty =
  let open Data_types in
  match ty with
  | Ty_prod _ -> false
  | _ -> true

let sub_types ty =
  let open Data_types in
  match ty with
  | Ty_prod ty_l -> ty_l
  | Ty_var _ | Ty_cond _ | Ty_scal _ -> [ty]

let sub_clocks arity ct =
  let open Clock_types in
  match ct with
  | Ct_prod ct_l ->
    assert (List.length ct_l = arity);
    ct_l
  | Ct_var _ | Ct_stream _ ->
    Utils.repeat arity ct

let get_sub_exps e =
  match e.e_desc with
  | E_var _ -> [e]
  | E_tuple e_l -> e_l
  | _ -> invalid_arg "get_sub_exps"

let rec simplify p e =
  let open Data_types in

  Format.eprintf "simplify %a %a@."
    print_pat p
    print_exp e
  ;

  let make_exp desc ty ct = make_exp ~loc:e.e_loc ty ct desc in

  let ty_l = sub_types e.e_info#ei_data in
  let arity = List.length ty_l in

  match p.p_desc with
  | P_split _ ->
    assert false (* lowered in preceding passes *)
  | P_var _ | P_spec_annot _ | P_type_annot _ | P_clock_annot _ ->
    assert (arity = 1);
    [p, e]
  | P_tuple p_l ->
    assert (arity = List.length p_l);
    let ct_l = sub_clocks arity e.e_info#ei_clock in
    match e.e_desc with
    | E_const _ ->
      assert false (* ill-typed *)
    | E_var _ ->
      assert false (* lowered above *)
    | E_fst _ | E_snd _ | E_fby _ | E_ifthenelse _ ->
      assert false (* lowered in preceding passes *)

    | E_tuple e_l ->
      simplify_list p_l e_l

    | E_app _ | E_where _ | E_dom _ | E_valof _
    | E_spec_annot _ | E_type_annot (_, (Ty_var _ | Ty_scal _ | Ty_cond _)) ->
      [p, e]

    | E_when (e, ce) ->
      let e_l = get_sub_exps e in
      let e_l = Utils.map3 (fun e -> make_exp (E_when (e, ce))) e_l ty_l ct_l in
      simplify_list p_l e_l

    | E_split (ce, e, ec_l) ->
      let e_l = get_sub_exps e in
      let e_l =
        Utils.map3 (fun e -> make_exp (E_split (ce, e, ec_l))) e_l ty_l ct_l
      in
      simplify_list p_l e_l

    | E_bmerge (ce, e1, e2) ->
      let e1_l = get_sub_exps e1 in
      let e2_l = get_sub_exps e2 in
      let e_l =
        Utils.map4
          (fun e1 e2 -> make_exp (E_bmerge (ce, e1, e2)))
          e1_l
          e2_l
          ty_l
          ct_l
      in
      simplify_list p_l e_l

    | E_merge (ce, c_l) ->
      let e_l = List.map (fun c -> c.c_body) c_l in
      let e_ll = List.map get_sub_exps e_l in
      let e_ll = Utils.transpose e_ll in
      let c_ll =
        List.map
          (fun e_l -> List.map2 (fun c e -> { c with c_body = e; }) c_l e_l)
          e_ll
      in
      let e_l =
        Utils.map3 (fun c_l -> make_exp (E_merge (ce, c_l))) c_ll ty_l ct_l
      in
      simplify_list p_l e_l

    | E_clock_annot (e, cka) ->
      let e_l = get_sub_exps e in
      let e_l =
        Utils.map3 (fun e -> make_exp (E_clock_annot (e, cka))) e_l ty_l ct_l
      in
      simplify_list p_l e_l

    | E_type_annot (_, Ty_prod _) ->
      (* TODO *)
      invalid_arg "unimplemented prod type ann"

    | E_buffer (e, bu) ->
      let e_l = get_sub_exps e in
      let e_l =
        Utils.map3 (fun e -> make_exp (E_buffer (e, bu))) e_l ty_l ct_l
      in
      simplify_list p_l e_l




and simplify_list p_l e_l =
  List.fold_left2 (fun acc p e -> simplify p e @ acc) [] p_l e_l

(* let rec map_sub_tuple mk acc e = *)
(*   match e.e_desc with *)
(*   | E_var _ -> mk e :: acc *)
(*   | E_tuple e_l -> List.fold_left (map_sub_tuple mk) acc e_l *)
(*   | _ -> invalid_arg "map_sub_tuple" *)

(* let tag_with_type l ty = *)
(*   let open Data_types in *)
(*   match ty with *)
(*   | Ty_prod ty_l -> ty_l *)
(*   | Ty_var _ | Ty_scal _ | Ty_cond _ -> List.map (fun x -> ty) l *)

(* let tag_with_clock l ct = *)
(*   let open Clock_types in *)
(*   match ct with *)
(*   | Ct_prod ct_l -> List.combine l ct_l *)
(*   | Ct_var _ | Ct_stream _ -> List.map (fun x -> x, ct) l *)

  (* let orig_p = p in *)
  (* let orig_e = e in *)
  (* match p.p_desc, e.e_desc with *)
  (* | P_split _, _ *)
  (* | _, (E_fst _ | E_snd _ | E_fby _ | E_ifthenelse _) *)
  (* | P_var _, E_tuple _ *)
  (* | P_tuple _, E_var _ *)
  (*   -> *)
  (*   assert false (\* lowered before *\) *)

  (* | P_tuple _, E_const _ -> *)
  (*   assert false (\* ill-typed *\) *)

  (* | P_var _, _ *)
  (* | P_tuple _, (E_app _ | E_where _) *)
  (*   -> *)
  (*   [p, e] *)

  (* | P_clock_annot (p, a), _ -> *)
  (*   let update (p, e) = *)
  (*     make_pat p.p_info#pi_data orig_p.p_info#pi_clock (P_clock_annot (p, a)), *)
  (*     e *)
  (*   in *)
  (*   List.map update (simplify p e) *)

  (* | P_type_annot (p, ty), _ -> *)
  (*   let update ((p, e), a) = *)
  (*     make_pat p.p_info#pi_data orig_p.p_info#pi_clock (P_type_annot (p, a)), *)
  (*     e *)
  (*   in *)
  (*   List.map update (tag_with_type (simplify p e) ty) *)

  (* | P_spec_annot (p, spec), _ -> *)
  (*   (\* We know that p is of scalar type *\) *)
  (*   let update (p, e) = { p with p_desc = P_spec_annot (p, spec); }, e in *)
  (*   List.map update (simplify p e) *)

  (* | P_tuple p_l, E_tuple e_l -> *)
  (*   simplify_list p_l e_l *)

  (* | P_tuple p_l, E_when (e, ce) -> *)
  (*   let mk (p, e) = { orig *)

and simplify_eq eqs eq =
  match eq.eq_desc with
  | Eq_plain (p, e) ->
    let pseudo_eqs = simplify p e in
    List.map (fun (p, e) -> make_plain_eq ~loc:eq.eq_loc p e) pseudo_eqs @ eqs
  | Eq_condvar _ -> eq :: eqs

and simplify_block block =
  let body = List.fold_left simplify_eq [] block.b_body in
  { block with b_body = body; }

let rec simplify_exp e =
  let e =
    match e.e_desc with
    | E_where (e', block) ->
      { e with e_desc = E_where (e', simplify_block block); }
    | _ ->
      e
  in
  SUB.map_sub_exp simplify_exp e

(** {2 Putting it all together} *)

let lower_file
    ctx
    (file :
     <
       interfaces : Interface.env;
       static_nodes : Acids_static.node_def list;
     >
       Acids_causal.file)
    =
  let env = initial_env file.f_info#interfaces in
  let file = apply_to_node_bodies (decompose_tuple_exp env) file in
  let file = apply_to_node_bodies remove_proj_exp file in
  let file = apply_to_node_bodies simplify_exp file in
  ctx, file

let pass =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_causal.print_file
       "lower_tuples"
       lower_file)
