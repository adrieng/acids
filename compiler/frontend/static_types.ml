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

type ty_scal =
  | S_static
  | S_dynamic

type ty =
  | Sy_var of int
  | Sy_scal of ty_scal
  | Sy_prod of ty list

type ty_sig = { input : ty; output : ty; }

let print_ty_scal fmt ss =
  match ss with
  | S_static -> Format.fprintf fmt "S"
  | S_dynamic -> Format.fprintf fmt "D"

let rec print_ty fmt sty =
  match sty with
  | Sy_var v -> Format.fprintf fmt "'s%d" v
  | Sy_scal ss -> print_ty_scal fmt ss
  | Sy_prod sty_l ->
    Format.fprintf fmt "(@[%a@])"
      (Utils.print_list_r print_ty " *") sty_l

let print_sig fmt csig =
  Format.fprintf fmt "@[%a -> %a@]"
    print_ty csig.input
    print_ty csig.output

let printing_prefix = "is"

let print_ty_scal_ann =
  Ast_misc.print_annot
    Compiler_options.print_static_info
    printing_prefix
    print_ty_scal

let print_ty_ann =
  Ast_misc.print_annot
    Compiler_options.print_static_info
    printing_prefix
    print_ty

let print_sig_ann =
  Ast_misc.print_annot
    Compiler_options.print_static_info
    printing_prefix
    print_sig

module PreTy =
struct
  type 'a pre_ty =
    | Psy_var of 'a
    | Psy_scal of ty_scal
    | Psy_prod of 'a pre_ty list

  let rec print print_var fmt pty =
    match pty with
    | Psy_var v -> print_var fmt v
    | Psy_scal ss -> print_ty_scal fmt ss
    | Psy_prod pty_l ->
      Format.fprintf fmt "(@[%a@])"
        (Utils.print_list_r (print print_var) " *") pty_l
end
module VarTy = Ast_misc.MakeVar(PreTy)

let instantiate_ty_sig fresh_ty tysig =
  let ht = Hashtbl.create 30 in

  let find_var v =
    try Hashtbl.find ht v
    with Not_found ->
      let ty = fresh_ty () in
      Hashtbl.add ht v ty;
      ty
  in

  let rec instantiate ty =
    match ty with
    | Sy_var v -> find_var v
    | Sy_scal ss -> PreTy.Psy_scal ss
    | Sy_prod ty_l -> PreTy.Psy_prod (List.map instantiate ty_l)
  in
  instantiate tysig.input, instantiate tysig.output

let rec ty_of_pre_ty pty =
  let open PreTy in
  match pty with
  | Psy_var v ->
    VarTy.ty_of_ty_var ty_of_pre_ty (fun v -> Sy_var v) v
  | Psy_scal ss -> Sy_scal ss
  | Psy_prod pty_l -> Sy_prod (List.map ty_of_pre_ty pty_l)

let make_ty_sig inp out =
  { input = ty_of_pre_ty inp; output = ty_of_pre_ty out; }

let rec is_static st =
  match st with
  | Sy_var _ -> false
  | Sy_scal S_static -> true
  | Sy_scal S_dynamic -> false
  | Sy_prod st_l -> List.exists is_static st_l

let is_static_signature ssig = is_static ssig.input

(** {2 Unification *)

open PreTy
open VarTy

type error =
  | Unification_conflict of Loc.t * t * t
  | Unification_occur of Loc.t * t

exception Unification_error of error

let print_error fmt err =
  match err with
  | Unification_conflict (l, ty1, ty2) ->
    Format.fprintf fmt "%aCould not unify %a with %a"
      Loc.print l
      VarTy.print ty1
      VarTy.print ty2
  | Unification_occur (l, ty) ->
    Format.fprintf fmt "%aType %a is cyclic"
      Loc.print l
      VarTy.print ty

let unification_conflict loc ty1 ty2 =
  raise (Unification_error (Unification_conflict (loc, ty1, ty2)))

let unification_occur loc ty =
  raise (Unification_error (Unification_occur (loc, ty)))

let occur_check loc id ty =
  let rec walk ty =
    match ty with
    | Psy_var { v_link = Some ty; } -> walk ty
    | Psy_var { v_link = None; v_id = id'; } ->
      if id = id' then unification_occur loc ty
    | Psy_scal _ -> ()
    | Psy_prod ty_l -> List.iter walk ty_l
  in
  match ty with
  | Psy_var { v_link = None; } -> ()
  | _ -> walk ty

let rec unify loc ty1 ty2 =
  match ty1, ty2 with
  (** traverse links *)
  | Psy_var { v_link = Some ty1; }, ty2
  | ty1, Psy_var { v_link = Some ty2; } -> unify loc ty1 ty2

    (** in-place unification *)
  | Psy_var ({ v_link = None; v_id = id; } as r), ty
  | ty, Psy_var ({ v_link = None; v_id = id; } as r) ->
    occur_check loc id ty;
    r.v_link <- Some ty

  | Psy_scal S_static, Psy_scal S_static
  | Psy_scal S_dynamic, Psy_scal S_dynamic ->
    ()

  | _ ->
    unification_conflict loc ty1 ty2

(** {2 Type constraints} *)

let rec unalias ty =
  let open PreTy in
  let open VarTy in
  match ty with
  | Psy_var { v_link = Some ty; } -> unalias ty
  | Psy_var { v_link = None; } | Psy_scal _ -> ty
  | Psy_prod ty_l -> Psy_prod (List.map unalias ty_l)

open PreTy
open VarTy

type constr =
  {
    lhs : t;
    rhs : t;
    loc : Loc.t;
  }

let print_constr fmt c =
  Format.fprintf fmt "@[%a <: %a@]"
    VarTy.print c.lhs
    VarTy.print c.rhs

let print_constr_system fmt cs =
  Format.fprintf fmt "@[<v 2>Worklist: %a@]"
    (Utils.print_list_r print_constr ",") cs;
  Format.fprintf fmt "@\nIdle queues:@\n";
  Utils.Int_map.print Utils.print_int print_constr

let make_constraint loc lhs rhs = { lhs = lhs; rhs = rhs; loc = loc; }

let take_var_idle_const idle i =
  try Utils.Int_map.find i idle, Utils.Int_map.remove i idle
  with Not_found -> [], idle

let rec awake_if_var idle ty =
  match unalias ty with
  | Psy_var { v_id = i; } -> take_var_idle_const idle i
  | Psy_scal _ -> [], idle
  | Psy_prod ty_l ->
    let add (awakened, idle) ty =
      let (new_awakened, idle) = awake_if_var idle ty in
      (awakened @ new_awakened, idle)
    in
    List.fold_left add ([], idle) ty_l

let add_constr idle c v =
  let v_idles, _ = take_var_idle_const idle v in
  Utils.Int_map.add v (c :: v_idles) idle

let print_solver_state fmt (worklist, waitlist) =
  Format.fprintf fmt "worklist: @[%a@]@\n"
    (Utils.print_list_r print_constr ";") worklist;
  Format.fprintf fmt "waitlist: @[%a@]"
    (Waitlist.print print_constr) waitlist

let solve ?(unify_remaining = true) constraints = (* TODO: solve incrementally *)
  let waitlist = Waitlist.create () in
  let rec solve worklist =
    match worklist with
    | [] -> ()
    | c :: worklist ->
      (
        let lhs = unalias c.lhs in
        let rhs = unalias c.rhs in
        let c = make_constraint c.loc lhs rhs in
        match lhs, rhs with
        | Psy_var { v_id = v1; }, Psy_var { v_id = v2; } ->
          Waitlist.add_item waitlist v1 c;
          Waitlist.merge_items waitlist v1 v2;
          solve worklist

        (* S <: D *)
        | Psy_scal S_static, Psy_scal S_dynamic
        | Psy_scal S_static, Psy_scal S_static
        | Psy_scal S_dynamic, Psy_scal S_dynamic ->
          solve worklist

        | Psy_scal S_dynamic, Psy_scal S_static ->
          unification_conflict c.loc lhs rhs

        (* ty <: S -> ty = S, D <: ty -> ty = D *)
        | Psy_var { v_id = v; }, Psy_scal S_static
        | Psy_scal S_dynamic, Psy_var { v_id = v; } ->
          let awakened_constraints = Waitlist.take_items waitlist v in
          unify c.loc lhs rhs;
          solve (awakened_constraints @ worklist)

        (* S <: ty and ty <: D are always satisfied *)
        | Psy_var { v_id = _; }, Psy_scal S_dynamic
        | Psy_scal S_static, Psy_var { v_id = _; } ->
          solve worklist

        (* Subtyping of products, a bit shaky *)
        | Psy_prod ty_l1, Psy_prod ty_l2 ->
          solve (List.map2 (make_constraint c.loc) ty_l1 ty_l2 @ worklist)
        (* I'm not sure of the following two rules *)
        | Psy_prod _, Psy_var { v_id = v; }
        | Psy_var { v_id = v; }, Psy_prod _ ->
          let awakened_constraints = Waitlist.take_items waitlist v in
          unify c.loc lhs rhs;
          solve (awakened_constraints @ worklist)

        | Psy_prod ty_l, Psy_scal _ ->
          let make ty = make_constraint c.loc ty rhs in
          solve (List.map make ty_l @ worklist)

        | Psy_scal _, Psy_prod ty_l ->
          let make ty = make_constraint c.loc lhs ty in
          solve (List.map make ty_l @ worklist)
      )
  in
  solve constraints;

  (* Unify the remaining constraints *)
  if unify_remaining
  then
    let remaining_constraints = Waitlist.take_all waitlist in
    let unify_constraints c = unify c.loc c.lhs c.rhs in
    List.iter unify_constraints remaining_constraints
