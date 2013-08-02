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

open Clock_types
open PreTySt
open PreTy

(** {2 Errors} *)

type error =
  | Occur_check_st of Loc.t * int * VarTySt.t
  | Occur_check_ty of Loc.t * int * VarTy.t
  | Could_not_unify_st of Loc.t * VarTySt.t * VarTySt.t
  | Could_not_unify_ty of Loc.t * VarTy.t * VarTy.t
  | Word_solver_error of Loc.t * Resolution.system * Resolution_errors.error

exception Resolution_error of error

let print_error fmt err =
  match err with
  | Occur_check_st (l, i, st) ->
    Format.fprintf fmt "%aStream type variable v%d occurs in %a"
      Loc.print l
      i
      VarTySt.print st
  | Occur_check_ty (l, i, ty) ->
    Format.fprintf fmt "%aClock type variable v%d occurs in %a"
      Loc.print l
      i
      VarTy.print ty
  | Could_not_unify_st (l, st1, st2) ->
    Format.fprintf fmt "%aCould not unify stream type %a with stream type %a"
      Loc.print l
      VarTySt.print st1
      VarTySt.print st2
  | Could_not_unify_ty (l, ty1, ty2) ->
    Format.fprintf fmt "%aCould not unify clock type %a with clock type %a"
      Loc.print l
      VarTy.print ty1
      VarTy.print ty2
  | Word_solver_error (l, wsys, err) ->
    Format.fprintf fmt
      "%aThe following system could not be solved@\n%a@\n%a"
      Loc.print l
      Resolution.print_system wsys
      Resolution_errors.print_error err

let occur_check_st l id st =
  raise (Resolution_error (Occur_check_st (l, id, st)))

let occur_check_ty l id ty =
  raise (Resolution_error (Occur_check_ty (l, id, ty)))

let could_not_unify_st l st1 st2 =
  raise (Resolution_error (Could_not_unify_st (l, st1, st2)))

let could_not_unify_ty l ty1 ty2 =
  raise (Resolution_error (Could_not_unify_ty (l, ty1, ty2)))

let word_solver_error l wsys err =
  raise (Resolution_error (Word_solver_error (l, wsys, err)))

(** {2 Utilities} *)

let print_system fmt sys =
  Format.fprintf fmt "{ @[<v>%a@] }"
    (Utils.print_list_r print_ty_constr ";") sys

let p f x =
  if !Compiler_options.print_clock_info
  then Format.printf "@[(*@[@ %a@]@ *)@]@." f x

let p_sys s sys =
  p
    (fun fmt sys -> Format.fprintf fmt "%s: %a" s print_system sys)
    sys

let occur_check_st loc id orig_st =
  let open VarTySt in
  let rec check st =
    match unalias_st st with
    | Pst_var { v_id = id'; } ->
      if id = id' then occur_check_st loc id orig_st
    | Pst_on (st, _) -> check st
  in
  match unalias_st orig_st with
  | Pst_var _ -> ()
  | Pst_on (st, _) -> check st

let occur_check_ty loc id orig_ty =
  let open VarTy in
  let rec check ty =
    match unalias_ty ty with
    | Pct_var { v_id = id'; } ->
      if id = id' then occur_check_ty loc id orig_ty
    | Pct_stream _ -> ()
    | Pct_prod ty_l -> List.iter check ty_l
  in
  match unalias_ty orig_ty with
  | Pct_var _ | Pct_stream _ -> ()
  | Pct_prod ty_l -> List.iter check ty_l

let rec is_rigid_ce ce =
  match ce with
  | Ce_condvar cev ->
    let rec has_stream_spec specs =
      let open Ast_misc in
      match specs with
      | [] -> false
      | (Unspec | Interval _) :: specs -> has_stream_spec specs
      | Word _ :: _ -> true
    in
    has_stream_spec cev.cev_specs
  | Ce_pword _ -> false
  | Ce_equal (ce, _) -> is_rigid_ce ce

let rec decompose_st st =
  match unalias_st st with
  | Pst_var _ -> st, []
  | Pst_on (bst, ce) ->
    if is_rigid_ce ce
    then st, []
    else
      let bst, ce_l = decompose_st bst in
      bst, ce :: ce_l

(* TODO cleaner *)
let rec ce_equal ce1 ce2 =
  match ce1, ce2 with
  | Ce_condvar v1, Ce_condvar v2 -> Ident.equal v1.cev_name v2.cev_name
  | Ce_pword pw1, Ce_pword pw2 -> pw1 = pw2
  | Ce_equal (ce1, ec1), Ce_equal (ce2, ec2) -> ec1 = ec2 && ce_equal ce1 ce2
  | _ -> false

let int_pword_of_econstr_pword env pw =
  Tree_word.map_upword (Interface.int_of_econstr env) (fun x -> x) pw

let rec eval_non_rigid_ce env ce =
  let open Ast_misc in
  match ce with
  | Ce_condvar cev ->
    let rec find_stream_spec specs =
      let open Ast_misc in
      match specs with
      | [] -> invalid_arg "eval_non_rigid_ce"
      | (Unspec | Interval _) :: specs -> find_stream_spec specs
      | Word p :: _ -> p
    in
    find_stream_spec cev.cev_specs
  | Ce_pword pw ->
    int_pword_of_econstr_pword env pw
  | Ce_equal (ce, ec) ->
    let p = eval_non_rigid_ce env ce in
    let i = Interface.int_of_econstr env ec in
    Ast_misc.map_upword (fun i' -> Int.of_bool (Int.equal i i')) (fun x -> x) p

let unit_ipword =
  let open Ast_misc in
  { u = Concat []; v = Concat [Leaf Int.one]; }

(** {2 Word constraints} *)

(** {2 Constraint simplification} *)

let simplify_equality_constraints sys =
  let unify_st loc sys st1 st2 =
    let open VarTySt in
    let st1 = unalias_st st1 in
    let st2 = unalias_st st2 in
    match st1, st2 with
    | Pst_var v1, Pst_var v2 ->
      if v1.v_id <> v2.v_id then v2.v_link <- Some st1;
      sys

    | Pst_var v, st | st, Pst_var v ->
      occur_check_st loc v.v_id st;
      v.v_link <- Some st;
      sys

    | Pst_on _, Pst_on _ ->
      { loc = loc; desc = Tc_equal_st (st1, st2); } :: sys
  in

  let rec unify_ty loc sys ty1 ty2 =
    let open VarTy in
    let ty1 = unalias_ty ty1 in
    let ty2 = unalias_ty ty2 in
    match ty1, ty2 with
    | Pct_var v1, Pct_var v2 ->
      if v1.v_id <> v2.v_id then v2.v_link <- Some ty1;
      sys

    | Pct_var v, ty | ty, Pct_var v ->
      occur_check_ty loc v.v_id ty;
      v.v_link <- Some ty;
      sys

    | Pct_stream st1, Pct_stream st2 ->
      unify_st loc sys st1 st2

    | Pct_prod ty_l1, Pct_prod ty_l2 ->
      if List.length ty_l1 <> List.length ty_l2
      then could_not_unify_ty loc ty1 ty2
      else List.fold_left2 (unify_ty loc) sys ty_l1 ty_l2

    | Pct_prod ty_l, Pct_stream st | Pct_stream st, Pct_prod ty_l ->
      synchronize loc sys st ty_l

  and synchronize loc sys st ty_l =
    let unif sys ty = unify_ty loc sys (Pct_stream st) ty in
    List.fold_left unif sys ty_l
  in

  let simplify_constraints sys c =
    match c.desc with
    | Tc_adapt _ -> c :: sys
    | Tc_equal (ty1, ty2) -> unify_ty c.loc sys ty1 ty2
    | Tc_equal_st (st1, st2) -> unify_st c.loc sys st1 st2
  in
  List.fold_left simplify_constraints [] sys

(** {2 Clock constraints to word constraints} *)

(*

  a1 on (10) = a2 on x

  ->

  a1' on c1 on (10) = a2 on x on (1)

  ->

  c1 on (10) = (1)
  and
  a1 = a2 on x

  ->

  c1 = (2)
  and
  a1 = a2 on x

  ------------------------------------------------------------------------------


  a1 on x on (10) = a2 on x on (2)

  ->

  a1' on c1 on (10) = a2 on x on (1)

  ->

  c1 on (10) = (1)
  and
  a1 = a2 on x

  ->

  c1 = (2)
  and
  a1 = a2 on x


*)

let fresh_word_var unknowns_ht =
  let s = "c" in
  let id = Ident.make_internal s in
  let cev =
    {
      cev_name = id;
      cev_bounds = Interval.singleton Int.zero; (* TODO *)
      cev_specs = [];
    }
  in
  Hashtbl.add unknowns_ht id cev;
  id, Ce_condvar cev

let word_constraints_of_clock_constraints env sys =
  let unknowns_ht = Hashtbl.create 100 in

  let rec unify loc wsys st1 st2 =
    let open VarTySt in
    let st1 = unalias_st st1 in
    let st2 = unalias_st st2 in
    match st1, st2 with
    | Pst_var v1, Pst_var v2 ->
      if v1.v_id <> v2.v_id then v2.v_link <- Some st1;
      wsys

    | Pst_var v, st | st, Pst_var v ->
      occur_check_st loc v.v_id st;
      v.v_link <- Some st;
      wsys

    | Pst_on (st1', ce1), Pst_on (st2', ce2)
      when is_rigid_ce ce1 && is_rigid_ce ce2 ->
      if not (ce_equal ce1 ce2) then could_not_unify_st loc st1' st2';
        unify loc wsys st1' st2'

    | Pst_on _, Pst_on _ ->
      unify_decompose Problem.Equal loc wsys st1 st2

  and unify_decompose kind loc wsys st1 st2 =
    let rigid_st1, left_consts = decompose st1 in
    let rigid_st2, right_consts = decompose st2 in
    let (bst1, v1), (bst2, v2) = gen_vars rigid_st1 rigid_st2 in
    let l_side = { Resolution.var = v1; Resolution.const = left_consts; } in
    let r_side = { Resolution.var = v2; Resolution.const = right_consts; } in
    let c =
      let open Resolution in
      { loc = loc; lhs = l_side; kind = kind; rhs = r_side; }
    in
    unify loc (c :: wsys) bst1 bst2

  and decompose st =
    let rigid_st, non_rigid_ce_l = decompose_st st in
    let iw_l =
      match non_rigid_ce_l with
      | [] -> [unit_ipword]
      | _ :: _ -> List.map (eval_non_rigid_ce env) non_rigid_ce_l
    in
    rigid_st, iw_l

  and gen_vars st1 st2 =
    let open VarTySt in
    match unalias_st st1, unalias_st st2 with
    | Pst_var v1, Pst_var v2 when v1.v_id = v2.v_id -> (* special case *)
      let bst = fresh_st () in
      let id, ce = fresh_word_var unknowns_ht in
      v1.v_link <- Some (Pst_on (bst, ce));
      (bst, Some (Ident.to_string id)), (bst, Some (Ident.to_string id))
    | _ ->
      gen_var st1, gen_var st2

  and gen_var st =
    match unalias_st st with
    | Pst_var v ->
      let bst = fresh_st () in
      let id, ce = fresh_word_var unknowns_ht in
      v.VarTySt.v_link <- Some (Pst_on (bst, ce));
      bst, Some (Ident.to_string id)
    | _ ->
      st, None
  in

  let solve_constraint wsys c =
    match c.desc with
    | Tc_equal _ -> invalid_arg "word_constraints_of_clock_constraints"

    | Tc_equal_st (st1, st2) ->
      unify c.loc wsys st1 st2

    | Tc_adapt (st1, st2) ->
      unify_decompose Problem.Adapt c.loc wsys st1 st2
  in

  {
    Resolution.body = List.fold_left solve_constraint [] sys;
    Resolution.options = Resolution_options.empty;
  },
  unknowns_ht

let add_options_to_word_constraints ?(check = false) pragma_env sys =
  let open Resolution_options in

  let initial_options = add empty (make "check" (Bool check)) in

  let add_pragma_if_possible _ p options =
    let open Pragma in
    match p.value with
    | Econstr (Ast_misc.Ec_bool b) -> add options (make p.key (Bool b))
    | Econstr (Ast_misc.Ec_int i) -> add options (make p.key (Int i))
    | _ -> options
  in

  let options =
    Utils.Env.fold add_pragma_if_possible pragma_env initial_options
  in

  { sys with Resolution.options = options; }

(** {2 Top-level function} *)

let solve_constraints env ctx pragma_env loc sys =
  p_sys "Initial system" sys;

  let sys = simplify_equality_constraints sys in
  p_sys "System with simplified equality constraints" sys;

  let wsys, unknowns_ht = word_constraints_of_clock_constraints env sys in

  let wsys =
    let debug = Pass_manager.ctx_get_attr ctx "debug" in
    add_options_to_word_constraints ~check:debug pragma_env wsys
  in

  p_sys "System with word variables" sys;
  p
    (fun fmt wsys ->
      Format.fprintf fmt "Word constraints: @[%a@]"
        Resolution.print_system wsys) wsys;

  (* Solve the system of inequations on words *)
  let sol =
    let open Resolution_errors in
    try Resolution.solve wsys
    with Could_not_solve err -> word_solver_error loc wsys err
  in

  (* Propagate the solutions back into the clocks *)
  let update_unknown v cev =
    match Resolution.Solution.get sol (Ident.to_string v) with
    | Some p ->
      cev.cev_specs <- Ast_misc.([Word p]);
      cev.cev_bounds <-
        let l, u = Ast_misc.bounds_of_int_pword p in
        Interval.make l u
    | None ->
      let err = "no solution to " ^ Ident.to_string v in
      Compiler.internal_error err
  in
  Hashtbl.iter update_unknown unknowns_ht;
