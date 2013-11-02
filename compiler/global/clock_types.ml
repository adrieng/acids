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
  | Ce_pword of Ast_misc.const_pword
  | Ce_equal of clock_exp * Ast_misc.econstr

and clock_exp_cond_var =
  {
    cecv_name : Ident.t;
    mutable cecv_bounds : Interval.t;
    mutable cecv_specs : Ast_misc.spec list;
  }

type 'a raw_stream_type =
  | St_var of 'a
  | St_on of 'a raw_stream_type * clock_exp

type stream_type = int raw_stream_type

type clock_type =
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

let beautify_clock_sig ct_sig =
  let make_st_var = Ast_misc.memoize_make_var (fun i -> St_var i) in

  let rec beautify_stream_type st =
    match st with
    | St_var i -> make_st_var i
    | St_on (st, ce) -> St_on (beautify_stream_type st, ce)
  in

  let rec beautify_clock_type ct =
    match ct with
    | Ct_stream st -> Ct_stream (beautify_stream_type st)
    | Ct_prod ct_l -> Ct_prod (List.map beautify_clock_type ct_l)
  in

  let beautify_constraint cstr =
    match cstr with
    | Cc_adapt (st1, st2) ->
      Cc_adapt (beautify_stream_type st1, beautify_stream_type st2)
    | Cc_equal (ct1, ct2) ->
      Cc_equal (beautify_clock_type ct1, beautify_clock_type ct2)
  in
  {
    ct_sig_input = beautify_clock_type ct_sig.ct_sig_input;
    ct_sig_output = beautify_clock_type ct_sig.ct_sig_output;
    ct_constraints = List.map beautify_constraint ct_sig.ct_constraints;
  }

let rec print_clock_exp fmt ce =
  match ce with
  | Ce_condvar cev ->
    Format.fprintf fmt "@[%a%a%a@]"
      Ident.print cev.cecv_name
      Ast_misc.print_interval_annot cev.cecv_bounds
      (Utils.print_list Ast_misc.print_spec_annot) cev.cecv_specs
  | Ce_pword pw ->
    Ast_misc.print_const_pword fmt pw
  | Ce_equal (ce, ec) ->
    Format.fprintf fmt "(%a = %a)"
      print_clock_exp ce
      Ast_misc.print_econstr ec

let rec print_raw_stream_type p fmt st =
  match st with
  | St_var v -> p fmt v
  | St_on (st, ce) ->
    Format.fprintf fmt "@[%a@ on %a@]"
      (print_raw_stream_type p) st
      print_clock_exp ce

let print_stream_type fmt st =
  let print_var fmt i =
    Format.fprintf fmt "'a%a" Utils.print_int_non_zero i
  in
  print_raw_stream_type print_var fmt st

let rec print_clock_type fmt ct =
  match ct with
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
  Format.fprintf fmt "@[%a ->@ %a%a@]"
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

let get_st ty =
  match ty with
  | Ct_prod _ -> invalid_arg "get_st: not a stream type"
  | Ct_stream st -> st

module PreCe =
struct
  type 'a pre_ty =
  | Pce_var of 'a
  | Pce_condvar of clock_exp_cond_var
  | Pce_pword of Ast_misc.const_pword
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
      Ast_misc.print_const_pword fmt pw
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

let rec st_of_pre_st make_st_var pst =
  let open PreTySt in
  match pst with
  | Pst_var v -> VarTySt.ty_of_ty_var (st_of_pre_st make_st_var) make_st_var v
  | Pst_on (st, pce) -> St_on (st_of_pre_st make_st_var st, ce_of_pre_ce pce)

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

let reset_st, fresh_st =
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () ->
    let v = !r in
    incr r;
    PreTySt.Pst_var { VarTySt.v_id = v; VarTySt.v_link = None; })

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

let rec ty_of_pre_ty make_st_var pty =
  let open PreTy in
  match pty with
  | Pct_var { VarTy.v_link = Some pty; } ->
    ty_of_pre_ty make_st_var pty
  | Pct_var ({ VarTy.v_link = None; } as v) ->
    let st = fresh_st () in
    v.VarTy.v_link <- Some (Pct_stream st);
    Ct_stream (st_of_pre_st make_st_var st)
  | Pct_stream pst ->
    Ct_stream (st_of_pre_st make_st_var pst)
  | Pct_prod pty_l ->
    Ct_prod (List.map (ty_of_pre_ty make_st_var) pty_l)

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

let reset_ty, fresh_ty =
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () ->
    let v = !r in
    incr r;
    PreTy.Pct_var { VarTy.v_id = v; VarTy.v_link = None; })

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

let clock_constr_of_ty_constr make_st_var cstr =
  match cstr.desc with
  | Tc_adapt (st1, st2) ->
    let st1 = st_of_pre_st make_st_var st1 in
    let st2 = st_of_pre_st make_st_var st2 in
    Cc_adapt (st1, st2)
  | Tc_equal (t1, t2) ->
    let t1 = ty_of_pre_ty make_st_var t1 in
    let t2 = ty_of_pre_ty make_st_var t2 in
    Cc_equal (t1, t2)
  | Tc_equal_st (st1, st2) ->
    let st1 = st_of_pre_st make_st_var st1 in
    let st2 = st_of_pre_st make_st_var st2 in
    Cc_equal (Ct_stream st1, Ct_stream st2)

let instantiate_clock_sig loc csig =
  let ht_st = Hashtbl.create 10 in

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

  let make_inst ht =
    let add_inst i x inst = (i, x) :: inst in
    Hashtbl.fold add_inst ht []
  in

  ty_in, ty_out, ty_constr, make_inst ht_st

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
    Some (Tree_word.map_upword Ast_misc.int_of_econstr (fun x -> x) p)
  | Ce_equal (ce, ec) ->
    let i = Ast_misc.int_of_econstr ec in
    match interp_ce ce with
    | None -> None
    | Some p ->
      Some
        (Tree_word.map_upword
           (fun i' -> Int.of_bool (0 = Utils.int_compare i i'))
           (fun x -> x)
           p)

let decompose_st_with_ce st =
  let rec walk acc st =
    match st with
    | St_var _ -> st, List.split acc
    | St_on (bst, ce) ->
      match interp_ce ce with
      | None -> st, List.split acc
      | Some p -> walk ((p, ce) :: acc) bst
  in
  walk [] st

(** [decompose_st st] decomposes a stream type into a pair of rigid base stream
    type * interpreted samplers *)
let decompose_st st =
  let st, (p_l, _) = decompose_st_with_ce st in
  st, p_l

let pword_of_econstr_tree pw =
  let pw = Tree_word.map_upword Ast_misc.int_of_econstr (fun x -> x) pw in
  Resolution_utils.pword_of_tree pw

let rec ce_compare ce1 ce2 =
  let tag_to_int ce =
    match ce with
    | Ce_condvar _ -> 0
    | Ce_pword _ -> 1
    | Ce_equal _ -> 2
  in
  match ce1, ce2 with
  | Ce_condvar v1, Ce_condvar v2 ->
    Ident.compare v1.cecv_name v2.cecv_name
  | Ce_pword pw1, Ce_pword pw2 ->
    let p1 = pword_of_econstr_tree pw1 in
    let p2 = pword_of_econstr_tree pw2 in
    if Pword.equal p1 p2 then 0 else 1
  | Ce_equal (ce1, ec1), Ce_equal (ce2, ec2) ->
    Utils.compare_both
      (Ast_misc.econstr_compare ec1 ec2)
      (fun () -> ce_compare ce1 ce2)
  | (Ce_condvar _ | Ce_pword _ | Ce_equal _), _ ->
    Utils.int_compare (tag_to_int ce1) (tag_to_int ce2)

let rec st_compare st1 st2 =
  let tag_to_int st =
    match st with
    | St_var _ -> 0
    | St_on _ -> 1
  in
  match st1, st2 with
  | St_var v1, St_var v2 -> Utils.int_compare v1 v2
  | St_on (st1, ce1), St_on (st2, ce2) ->
    Utils.compare_both
      (ce_compare ce1 ce2)
      (fun () -> st_compare st1 st2)
  | (St_var _ | St_on _), _ ->
    Utils.int_compare (tag_to_int st1) (tag_to_int st2)

let rec ct_compare ct1 ct2 =
  let tag_to_int ct =
    match ct with
    | Ct_stream _ -> 0
    | Ct_prod _ -> 1
  in
  match ct1, ct2 with
  | Ct_stream st1, Ct_stream st2 ->
    st_compare st1 st2
  | Ct_prod ct_l1, Ct_prod ct_l2 ->
    Utils.list_compare ct_compare ct_l1 ct_l2
  | (Ct_stream _ | Ct_prod _), _ ->
    Utils.int_compare (tag_to_int ct1) (tag_to_int ct2)

let rec flatten_clock_type acc ct =
  match ct with
  | Ct_stream st -> st :: acc
  | Ct_prod ct_l -> List.fold_left flatten_clock_type acc ct_l

let rec map_stream_type f st =
  match st with
  | St_var i -> St_var (f i)
  | St_on (st, ce) -> St_on (map_stream_type f st, ce)

let map_stream_type_of_sig f ty_sig =
  let rec map_ty ty =
    match ty with
    | Ct_stream st -> Ct_stream (f st)
    | Ct_prod ty_l -> Ct_prod (List.map map_ty ty_l)
  in
  {
    ty_sig with
      ct_sig_input = map_ty ty_sig.ct_sig_input;
      ct_sig_output = map_ty ty_sig.ct_sig_output;
  }

let ce_pword_of_pword p =
  let p = Pword.to_tree_pword p in
  let p = Tree_word.map_upword (fun i -> Ast_misc.Ec_int i) (fun i -> i) p in
  Ce_pword p

(* Remove ... on (1) ... from stream types *)
let rec simplify_on_one_st st =
  match st with
  | St_var _ -> st
  | St_on (st, ce) ->
    (
      match interp_ce ce with
      | None -> St_on (simplify_on_one_st st, ce)
      | Some p ->
        let p = Resolution_utils.pword_of_tree p in
        if Pword.is_unit_pword p
        then simplify_on_one_st st
        else St_on (simplify_on_one_st st, ce)
    )

(* Compute ONs when it leads to shorter words *)
let simplify_on_st ?(u_factor = 1) ?(v_factor = 1) st =
  let rec simplify st =
    let st, (p_l, ce_l) = decompose_st_with_ce st in

    match p_l with
    | [] -> skip_noninterp st
    | _ :: _ ->
      let total_ce_u_size, total_ce_v_size =
        let total_ce_u_size, total_ce_v_size =
          List.fold_left
            (fun (x, y) (a, b) -> x + a, y + b)
            (0, 0)
            (List.map Tree_word.size_upword p_l)
        in
        Int.of_int (u_factor * total_ce_u_size),
        Int.of_int (v_factor * total_ce_v_size)
      in

      let p_l = List.map Resolution_utils.pword_of_tree p_l in
      let p = Utils.fold_left_1 Pword.on p_l in

      let on_u_size, on_v_size = Pword.(size p.u, size p.v) in

      if Int.(total_ce_u_size + total_ce_v_size <= on_u_size + on_v_size)
      then List.fold_left (fun st ce -> St_on (st, ce)) (skip_noninterp st) ce_l
      else
        St_on (skip_noninterp st, ce_pword_of_pword p)

  and skip_noninterp st =
    match st with
    | St_var _ -> st
    | St_on (st, ce) ->
      assert (interp_ce ce = None);
      St_on (simplify st, ce)
  in

  simplify st

let rec simplify_prefix_st st =
  let rec simplify_prefix_ce ce =
    match ce with
    | Ce_condvar _ -> ce
    | Ce_pword pw ->
      let p = pword_of_econstr_tree pw in
      let p = Pword.pull_prefix_in p in
      ce_pword_of_pword p
    | Ce_equal (ce, se) -> Ce_equal (simplify_prefix_ce ce, se)
  in

  match st with
  | St_var _ -> st
  | St_on (st, ce) -> St_on (simplify_prefix_st st, simplify_prefix_ce ce)

let simplify_sig ty_sig =
  let ty_sig = map_stream_type_of_sig simplify_on_one_st ty_sig in
  let ty_sig = map_stream_type_of_sig simplify_on_st ty_sig in
  let ty_sig = map_stream_type_of_sig simplify_prefix_st ty_sig in
  ty_sig

let generalize_clock_sig inp out cstrs =
  let make_st_var = Ast_misc.memoize_make_var (fun i -> St_var i) in
  let ty_sig =
    {
      ct_sig_input = ty_of_pre_ty make_st_var inp;
      ct_sig_output = ty_of_pre_ty make_st_var out;
      ct_constraints = List.map (clock_constr_of_ty_constr make_st_var) cstrs;
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

let decompose_pword st =
  let bst, p_l = decompose_st st in
  let p_l = List.map Resolution_utils.pword_of_tree p_l in
  bst, List.fold_left Pword.on Pword.unit_pword p_l

let non_strict_adaptable st1 st2 =
  let bst1, p1 = decompose_pword st1 in
  let _, p2 = decompose_pword st2 in
  (* TODO check bst1 = bst2 *)
  Pword.adapt ~delay:(max_burst_stream_type bst1) p1 p2

let binary_stream_type st = Int.(max_burst_stream_type st <= one)

let rec binary_clock_type ty =
  match ty with
  | Ct_prod ty_l -> List.fold_left (&&) true (List.map binary_clock_type ty_l)
  | Ct_stream st -> binary_stream_type st

let buffer_size inp_st out_st =
  let _, p1 = decompose_pword inp_st in
  let _, p2 = decompose_pword out_st in
  (* TODO check bst1 = bst2 *)
  Pword.buffer_size p1 p2

let st_of_synchronized_ct ct =
  let st_l = flatten_clock_type [] ct in
  match st_l with
  | [] ->
    invalid_arg "clock_types_of_synchronized_ty: nullary product"
  | st :: st_l ->
    (* TODO: be smarter? *)
    List.iter (fun st' -> assert (0 = st_compare st st')) st_l;
    st

(* Clock variable stuff *)

type var_kind = Var_stream of int

let var_kind_compare (Var_stream i1) (Var_stream i2) =
  Utils.int_compare i1 i2

module VarKindSet =
  Set.Make(struct type t = var_kind let compare = var_kind_compare end)

let rec base_stream_var st =
  match st with
  | St_var i -> Var_stream i
  | St_on (st, _) -> base_stream_var st

let rec base_ty_var vars ty =
  match ty with
  | Ct_stream st -> VarKindSet.add (base_stream_var st) vars
  | Ct_prod ty_l -> List.fold_left base_ty_var vars ty_l

let base_sig_vars ty_sig =
  base_ty_var
    (base_ty_var VarKindSet.empty ty_sig.ct_sig_input)
    ty_sig.ct_sig_output

let rec base_var_of_stream_type st =
  match st with
  | St_var i -> i
  | St_on (st, _) -> base_var_of_stream_type st

let slice_signature ?(compare = (=)) base_var cksig =
  let is_on_base_var st =
    let base_var_st = base_var_of_stream_type st in
    compare base_var_st base_var
  in

  let inputs = flatten_clock_type [] cksig.ct_sig_input in
  let outputs = flatten_clock_type [] cksig.ct_sig_output in
  List.(rev (filter is_on_base_var inputs), rev (filter is_on_base_var outputs))
