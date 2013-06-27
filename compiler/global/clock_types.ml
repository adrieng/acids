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
  | Ce_var of Ident.t
  | Ce_pword of (Ast_misc.econstr list, Int.t) Ast_misc.upword
  | Ce_equal of clock_exp * Ast_misc.econstr
  | Ce_iter of clock_exp

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
  | Ce_var id -> Ident.print fmt id
  | Ce_pword pw ->
    let print_fword fmt fw =
      match fw with
      | [x] -> Ast_misc.print_econstr fmt x
      | _ ->
        Format.fprintf fmt "'%a'"
          (Utils.print_list Ast_misc.print_econstr) fw
    in
    Ast_misc.print_upword print_fword Int.print fmt pw
  | Ce_equal (ce, ec) ->
    Format.fprintf fmt "%a = %a"
      print_clock_exp ce
      Ast_misc.print_econstr ec
  | Ce_iter ce ->
    Format.fprintf fmt "iter %a" print_clock_exp ce

let rec print_stream_type fmt st =
  match st with
  | St_var i -> Format.fprintf fmt "'a%d" i
  | St_on (st, ce) ->
    Format.fprintf fmt "@[%a@ on %a@]"
      print_stream_type st
      print_clock_exp ce

let rec print_clock_type fmt ct =
  match ct with
  | Ct_var i -> Format.fprintf fmt "'b%d" i
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

module PreTySt =
struct
  type 'a pre_ty =
    | Pst_var of 'a
    | Pst_on of 'a pre_ty * clock_exp

  let rec print print_var fmt pty =
    match pty with
    | Pst_var v -> print_var fmt v
    | Pst_on (pty, ce) ->
      Format.fprintf fmt "@[%a@ on %a@]"
        (print print_var) pty
        print_clock_exp ce
end
module VarTySt = Ast_misc.MakeVar(PreTySt)

let rec st_of_pre_st pst =
  let open PreTySt in
  match pst with
  | Pst_var v -> VarTySt.ty_of_ty_var st_of_pre_st (fun i -> St_var i) v
  | Pst_on (st, ce) -> St_on (st_of_pre_st st, ce)

module PreTy =
struct
  type 'a pre_ty =
    | Pct_var of 'a
    | Pct_stream of VarTySt.ty_var PreTySt.pre_ty
    | Pct_prod of 'a pre_ty list

  let rec print print_var fmt pty =
    match pty with
    | Pct_var v -> print_var fmt v
    | Pct_stream pst -> PreTySt.print VarTySt.print_var fmt pst
    | Pct_prod pty_l ->
      Format.fprintf fmt "(@[%a@])"
        (Utils.print_list_r (print print_var) " *") pty_l

end
module VarTy = Ast_misc.MakeVar(PreTy)

let rec ty_of_pre_ty pty =
  let open PreTy in
  match pty with
  | Pct_var v -> VarTy.ty_of_ty_var ty_of_pre_ty (fun i -> Ct_var i) v
  | Pct_stream pst -> Ct_stream (st_of_pre_st pst)
  | Pct_prod pty_l -> Ct_prod (List.map ty_of_pre_ty pty_l)

type ty_constr_desc =
  | Tc_adapt of VarTySt.t * VarTySt.t (* st1 <: st2 *)
  | Tc_equal of VarTy.t * VarTy.t (* ty1 = ty2 *)

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

let print_ty_constr fmt tyc =
  print_ty_constr_desc fmt tyc.desc

let clock_constr_of_ty_constr cstr =
  match cstr.desc with
  | Tc_adapt (st1, st2) ->
    let st1 = st_of_pre_st st1 in
    let st2 = st_of_pre_st st2 in
    Cc_adapt (st1, st2)
  | Tc_equal (t1, t2) ->
    let t1 = ty_of_pre_ty t1 in
    let t2 = ty_of_pre_ty t2 in
    Cc_equal (t1, t2)

let generalize_clock_sig inp out cstrs =
  {
    ct_sig_input = ty_of_pre_ty inp;
    ct_sig_output = ty_of_pre_ty out;
    ct_constraints = List.map clock_constr_of_ty_constr cstrs;
  }

let instantiate_clock_sig loc fresh_st fresh_ct csig =
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
    | St_on (st, ce) -> Pst_on (inst_st st, ce)
  in

  let rec inst_ct ct =
    let open PreTy in
    match ct with
    | Ct_var v ->
      (
        try Hashtbl.find ht_ct v
        with Not_found ->
          let ct = fresh_ct () in
          Hashtbl.add ht_ct v ct;
          ct
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
