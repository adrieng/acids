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

type clock_exp =
  | Ce_condvar of clock_exp_cond_var
  | Ce_pword of (Ast_misc.econstr, Int.t) Ast_misc.t
  | Ce_equal of clock_exp * Ast_misc.econstr

and clock_exp_cond_var =
  {
    cecv_name : Ident.t;
    mutable cecv_bounds : Interval.t;
    mutable cecv_specs : Ast_misc.spec list;
  }

type stream_type =
  | St_var of int
  | St_on of stream_type * clock_exp

type clock_type =
  | Ct_var of int
  | Ct_stream of stream_type
  | Ct_prod of clock_type list

type clock_constraint =
  | Cc_adapt of stream_type * stream_type
  | Cc_equal of clock_type * clock_type

type clock_sig =
    {
      ct_sig_input : clock_type;
      ct_sig_output : clock_type;
      ct_constraints : clock_constraint list;
    }

let rec print_clock_exp fmt ce =
  match ce with
  | Ce_condvar cev ->
    Format.fprintf fmt "@[%a%a%a@]"
      Ident.print cev.cecv_name
      Ast_misc.print_interval_annot cev.cecv_bounds
      (Utils.print_list Ast_misc.print_spec_annot) cev.cecv_specs
  | Ce_pword pw ->
    Ast_misc.print_upword_int Ast_misc.print_econstr fmt pw
  | Ce_equal (ce, ec) ->
    Format.fprintf fmt "(%a = %a)"
      print_clock_exp ce
      Ast_misc.print_econstr ec

let rec print_stream_type fmt st =
  match st with
  | St_var i -> Format.fprintf fmt "'a%a" Utils.print_int_non_zero i
  | St_on (st, ce) ->
    Format.fprintf fmt "@[%a@ on %a@]"
      print_stream_type st
      print_clock_exp ce

let rec print_clock_type fmt ct =
  match ct with
  | Ct_var i -> Format.fprintf fmt "'b%a" Utils.print_int_non_zero i
  | Ct_stream st -> print_stream_type fmt st
  | Ct_prod st_l ->
    Format.fprintf fmt "(@[%a@])"
      (Utils.print_list_r print_clock_type " *") st_l

let print_constraint fmt c =
  match c with
  | Cc_adapt (st1, st2) ->
    Format.fprintf fmt "@[%a <:@ %a@]"
      print_stream_type st1
      print_stream_type st2
  | Cc_equal (t1, t2) ->
    Format.fprintf fmt "@[%a =@ %a@]"
      print_clock_type t1
      print_clock_type t2

let print_sig fmt cs =
  let print_constraints fmt cs =
    match cs with
    | [] -> ()
    | _ :: _ ->
      Format.fprintf fmt "@ with {@[%a@]}"
        (Utils.print_list_r print_constraint ",") cs
  in
  Format.fprintf fmt "@[%a -> %a%a@]"
    print_clock_type cs.ct_sig_input
    print_clock_type cs.ct_sig_output
    print_constraints cs.ct_constraints

let printing_prefix = "::"

let print_stream_type_ann =
  Ast_misc.print_annot
    Compiler_options.print_clock_info
    printing_prefix
    print_stream_type

let print_clock_type_ann =
  Ast_misc.print_annot
    Compiler_options.print_clock_info
    printing_prefix
    print_clock_type

let print_sig_ann =
  Ast_misc.print_annot
    Compiler_options.print_clock_info
    printing_prefix
    print_sig

module PreCe =
struct
  type 'a pre_ty =
  | Pce_var of 'a
  | Pce_condvar of clock_exp_cond_var
  | Pce_pword of (Ast_misc.econstr, Int.t) Ast_misc.t
  | Pce_equal of 'a pre_ty * Ast_misc.econstr

  let rec print print_var fmt pce =
    match pce with
    | Pce_var v -> print_var fmt v
    | Pce_condvar pcv ->
      Format.fprintf fmt "@[%a%a%a@]"
        Ident.print pcv.cecv_name
        Ast_misc.print_interval_annot pcv.cecv_bounds
        (Utils.print_list Ast_misc.print_spec_annot) pcv.cecv_specs
    | Pce_pword pw ->
      Ast_misc.print_upword_int Ast_misc.print_econstr fmt pw
    | Pce_equal (pce, ec) ->
      Format.fprintf fmt "(%a = %a)"
        (print print_var) pce
        Ast_misc.print_econstr ec

  let var_pref = "ce"
end
module VarCe = Ast_misc.MakeVar(PreCe)

let rec ce_of_pre_ce pce =
  let open PreCe in
  match pce with
  | Pce_var v ->
    VarCe.ty_of_ty_var
      ce_of_pre_ce
      (fun _ -> invalid_arg "ce_of_pre_ce: Pce_var _")
      v
  | Pce_condvar cev -> Ce_condvar cev
  | Pce_pword p -> Ce_pword p
  | Pce_equal (pce, ec) -> Ce_equal (ce_of_pre_ce pce, ec)

let rec pre_ce_of_ce ce =
  let open PreCe in
  match ce with
  | Ce_condvar cev -> Pce_condvar cev
  | Ce_pword p -> Pce_pword p
  | Ce_equal (ce, ec) -> Pce_equal (pre_ce_of_ce ce, ec)

let rec unalias_ce pce =
  let open PreCe in
  let open VarCe in
  match pce with
  | Pce_var ({ v_link = Some pce; } as r) ->
    let pce = unalias_ce pce in
    r.v_link <- Some pce;
    pce
  | _ ->
    pce

module PreTySt =
struct
  type 'a pre_ty =
    | Pst_var of 'a
    | Pst_on of 'a pre_ty * VarCe.t

  let rec print print_var fmt pty =
    match pty with
    | Pst_var v -> print_var fmt v
    | Pst_on (pty, pce) ->
      Format.fprintf fmt "@[%a@ on %a@]"
        (print print_var) pty
        VarCe.print pce

  let var_pref = "a"
end
module VarTySt = Ast_misc.MakeVar(PreTySt)

let make_st_var i = St_var i

let rec st_of_pre_st ?(make_st_var = make_st_var) pst =
  let open PreTySt in
  match pst with
  | Pst_var v -> VarTySt.ty_of_ty_var (st_of_pre_st ~make_st_var) make_st_var v
  | Pst_on (st, pce) -> St_on (st_of_pre_st ~make_st_var st, ce_of_pre_ce pce)

let rec unalias_st st =
  let open PreTySt in
  let open VarTySt in
  match st with
  | Pst_var ({ v_link = Some st; } as r) ->
    let st = unalias_st st in
    r.v_link <- Some st;
    st
  | _ ->
    st

module PreTy =
struct
  type 'a pre_ty =
    | Pct_var of 'a
    | Pct_stream of VarTySt.t
    | Pct_prod of 'a pre_ty list

  let rec print print_var fmt pty =
    match pty with
    | Pct_var v -> print_var fmt v
    | Pct_stream pst -> PreTySt.print VarTySt.print_var fmt pst
    | Pct_prod pty_l ->
      Format.fprintf fmt "(@[%a@])"
        (Utils.print_list_r (print print_var) " *") pty_l

  let var_pref = "b"
end
module VarTy = Ast_misc.MakeVar(PreTy)

let make_ty_var i = Ct_var i

let rec ty_of_pre_ty
    ?(make_st_var = make_st_var)
    ?(make_ty_var = make_ty_var)
    pty =
  let open PreTy in
  match pty with
  | Pct_var v ->
    VarTy.ty_of_ty_var (ty_of_pre_ty ~make_st_var ~make_ty_var) make_ty_var v
  | Pct_stream pst ->
    Ct_stream (st_of_pre_st ~make_st_var pst)
  | Pct_prod pty_l ->
    Ct_prod (List.map (ty_of_pre_ty ~make_ty_var) pty_l)

let rec unalias_ty ty =
  let open PreTy in
  let open VarTy in
  match ty with
  | Pct_var ({ v_link = Some ty; } as r) ->
    let ty = unalias_ty ty in
    r.v_link <- Some ty;
    ty
  | _ ->
    ty

type ty_constr_desc =
  | Tc_adapt of VarTySt.t * VarTySt.t (* st1 <: st2 *)
  | Tc_equal of VarTy.t * VarTy.t (* ty1 = ty2 *)
  | Tc_equal_st of VarTySt.t * VarTySt.t (* st1 = st2 *)

type ty_constr =
  {
    loc : Loc.t;
    desc : ty_constr_desc;
  }

let print_ty_constr_desc fmt tycd =
  match tycd with
  | Tc_adapt (st1, st2) ->
    Format.fprintf fmt "@[%a <:@ %a@]"
      VarTySt.print st1
      VarTySt.print st2
  | Tc_equal (t1, t2) ->
    Format.fprintf fmt "@[%a =@ %a@]"
      VarTy.print t1
      VarTy.print t2
  | Tc_equal_st (st1, st2) ->
    Format.fprintf fmt "@[%a =@ %a@]"
      VarTySt.print st1
      VarTySt.print st2

let print_ty_constr fmt tyc =
  print_ty_constr_desc fmt tyc.desc

let clock_constr_of_ty_constr
    ?(make_st_var = make_st_var)
    ?(make_ty_var = make_ty_var)
    cstr =
  match cstr.desc with
  | Tc_adapt (st1, st2) ->
    let st1 = st_of_pre_st ~make_st_var st1 in
    let st2 = st_of_pre_st ~make_st_var st2 in
    Cc_adapt (st1, st2)
  | Tc_equal (t1, t2) ->
    let t1 = ty_of_pre_ty ~make_st_var ~make_ty_var t1 in
    let t2 = ty_of_pre_ty ~make_st_var ~make_ty_var t2 in
    Cc_equal (t1, t2)
  | Tc_equal_st (st1, st2) ->
    let st1 = st_of_pre_st ~make_st_var st1 in
    let st2 = st_of_pre_st ~make_st_var st2 in
    Cc_equal (Ct_stream st1, Ct_stream st2)

let reset_st, fresh_st =
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () ->
    let v = !r in
    incr r;
    PreTySt.Pst_var { VarTySt.v_id = v; VarTySt.v_link = None; })

let reset_ty, fresh_ty =
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () ->
    let v = !r in
    incr r;
    PreTy.Pct_var { VarTy.v_id = v; VarTy.v_link = None; })

let instantiate_clock_sig loc csig =
  let ht_st = Hashtbl.create 10 in
  let ht_ct = Hashtbl.create 10 in

  let rec inst_st st =
    let open PreTySt in
    match st with
    | St_var v ->
      (
        try Hashtbl.find ht_st v
        with Not_found ->
          let st = fresh_st () in
          Hashtbl.add ht_st v st;
          st
      )
    | St_on (st, ce) -> Pst_on (inst_st st, pre_ce_of_ce ce)
  in

  let rec inst_ct ct =
    let open PreTy in
    match ct with
    | Ct_var v ->
      (
        try Hashtbl.find ht_ct v
        with Not_found ->
          let ty = fresh_ty () in
          Hashtbl.add ht_ct v ty;
          ty
      )
    | Ct_stream st -> Pct_stream (inst_st st)
    | Ct_prod ct_l -> Pct_prod (List.map inst_ct ct_l)
  in

  let inst_constraint c =
    let desc =
      match c with
      | Cc_adapt (st1, st2) ->
        Tc_adapt (inst_st st1, inst_st st2)
      | Cc_equal (t1, t2) ->
        Tc_equal (inst_ct t1, inst_ct t2)
    in
    { loc = loc; desc = desc; }
  in

  let ty_in = inst_ct csig.ct_sig_input in
  let ty_out = inst_ct csig.ct_sig_output in
  let ty_constr = List.map inst_constraint csig.ct_constraints in
  let insts =
    let add_inst i ty inst_l = (i, ty) :: inst_l in
    Hashtbl.fold add_inst ht_st []
  in
  ty_in, ty_out, ty_constr, (insts : (int * VarTySt.t) list)

let rec reroot_st bst st =
  let open PreTySt in
  match st with
  | Pst_var { VarTySt.v_link = Some st; } -> reroot_st bst st
  | Pst_var _ -> bst
  | Pst_on (st, cce) -> Pst_on (reroot_st bst st, cce)

let rec reroot_ty bst ty =
  let open PreTy in
  match ty with
  | Pct_var { VarTy.v_link = Some ty; } -> reroot_ty bst ty
  | Pct_var _ -> ty
  | Pct_stream st -> Pct_stream (reroot_st bst st)
  | Pct_prod ty_l -> Pct_prod (List.map (reroot_ty bst) ty_l)

let rec interp_ce ce =
  match ce with
  | Ce_condvar cev ->
    let rec has_full_spec specs =
      let open Ast_misc in
      match specs with
      | [] -> None
      | Word p :: _ -> Some p
      | (Unspec | Interval _) :: specs -> has_full_spec specs
    in
    has_full_spec cev.cecv_specs
  | Ce_pword p ->
    Some (Ast_misc.map_upword Ast_misc.int_of_econstr (fun x -> x) p)
  | Ce_equal (ce, ec) ->
    let i = Ast_misc.int_of_econstr ec in
    match interp_ce ce with
    | None -> None
    | Some p ->
      Some
        (Ast_misc.map_upword
           (fun i' -> Int.of_bool (0 = Utils.int_compare i i'))
           (fun x -> x)
           p)

let rec simplify_st st =
  match st with
  | St_var _ -> st
  | St_on (st, ce) ->
    (
      match interp_ce ce with
      | None -> St_on (simplify_st st, ce)
      | Some p ->
        let p = Resolution_utils.pword_of_tree p in
        if Pword.is_unit_pword p
        then simplify_st st
        else St_on (simplify_st st, ce)
    )

let rec simplify_ty ty =
  match ty with
  | Ct_var _ -> ty
  | Ct_stream st -> Ct_stream (simplify_st st)
  | Ct_prod ty_l -> Ct_prod (List.map simplify_ty ty_l)

let simplify_sig ty_sig =
  {
    ty_sig with
      ct_sig_input = simplify_ty ty_sig.ct_sig_input;
      ct_sig_output = simplify_ty ty_sig.ct_sig_output;
  }

let generalize_clock_sig inp out cstrs =
  let make_st_var = Ast_misc.memoize_make_var (fun i -> St_var i) in
  let make_ty_var = Ast_misc.memoize_make_var (fun i -> Ct_var i) in
  let ty_sig =
    {
      ct_sig_input = ty_of_pre_ty ~make_st_var ~make_ty_var inp;
      ct_sig_output = ty_of_pre_ty ~make_st_var ~make_ty_var out;
      ct_constraints =
        List.map (clock_constr_of_ty_constr ~make_st_var ~make_ty_var) cstrs;
    }
  in
  simplify_sig ty_sig

let rec max_burst_stream_type st =
  let open Int in
  match st with
  | St_var _ -> one
  | St_on (st, ce) ->
    let upper_bound_ce =
      match ce with
      | Ce_condvar cev -> cev.cecv_bounds.Interval.u
      | Ce_pword pw ->
        let p = Tree_word.map_upword Ast_misc.int_of_econstr (fun x -> x) pw in
        snd (Ast_misc.bounds_of_int_pword p)
      | Ce_equal _ -> Int.one
    in
    upper_bound_ce * max_burst_stream_type st

let decompose_st st =
  let rec walk acc st =
    match st with
    | St_var _ -> st, acc
    | St_on (bst, ce) ->
      match interp_ce ce with
      | None -> st, acc
      | Some p -> walk (p :: acc) bst
  in
  walk [] st

let non_strict_adaptable st1 st2 =
  let bst1, p_l1 = decompose_st st1 in
  let _, p_l2 = decompose_st st2 in
  (* TODO check bst1 = bst2 *)
  let delay = max_burst_stream_type bst1 in

  let p_l1 = List.map Resolution_utils.pword_of_tree p_l1 in
  let p_l2 = List.map Resolution_utils.pword_of_tree p_l2 in

  let p1 = List.fold_left Pword.on Pword.unit_pword p_l1 in
  let p2 = List.fold_left Pword.on Pword.unit_pword p_l2 in

  Pword.adapt ~delay p1 p2

let binary_stream_type st = Int.(max_burst_stream_type st <= one)

let rec binary_clock_type ty =
  match ty with
  | Ct_var _ -> true
  | Ct_prod ty_l -> List.fold_left (&&) true (List.map binary_clock_type ty_l)
  | Ct_stream st -> binary_stream_type st
