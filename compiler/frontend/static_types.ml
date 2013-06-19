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
  | Sy_scal of ty_scal
  | Sy_prod of ty list

type ty_sig = { input : ty; output : ty; }

let print_static_ty_scal fmt ss =
  match ss with
  | S_static -> Format.fprintf fmt "S"
  | S_dynamic -> Format.fprintf fmt "D"

let rec print_static_ty fmt sty =
  match sty with
  | Sy_scal ss -> print_static_ty_scal fmt ss
  | Sy_prod sty_l ->
    Format.fprintf fmt "(@[%a@])"
      (Utils.print_list_r print_static_ty " *") sty_l

let print_sig fmt csig =
  Format.fprintf fmt "@[%a -> %a@]"
    print_static_ty csig.input
    print_static_ty csig.output

module PreTy =
struct
  type 'a pre_ty =
    | Psy_var of 'a
    | Psy_scal of ty_scal
    | Psy_prod of 'a pre_ty list

  let rec print print_var fmt pty =
    match pty with
    | Psy_var v -> print_var fmt v
    | Psy_scal ss -> print_static_ty_scal fmt ss
    | Psy_prod pty_l ->
      Format.fprintf fmt "(@[%a@])"
        (Utils.print_list_r (print print_var) " *") pty_l
end
module VarTy = Ast_misc.MakeVar(PreTy)

let instantiate_ty_sig tysig =
  let rec instantiate ty =
    match ty with
    | Sy_scal ss -> PreTy.Psy_scal ss
    | Sy_prod ty_l -> PreTy.Psy_prod (List.map instantiate ty_l)
  in
  instantiate tysig.input, instantiate tysig.output

let rec ty_of_pre_ty pty =
  let open PreTy in
  match pty with
  | Psy_var v ->
    (* type variables default to dynamic since its more modular *)
    VarTy.ty_of_ty_var ty_of_pre_ty (fun _ -> Sy_scal S_dynamic) v
  | Psy_scal ss -> Sy_scal ss
  | Psy_prod pty_l -> Sy_prod (List.map ty_of_pre_ty pty_l)

let make_ty_sig inp out = { input = ty_of_pre_ty inp; output = ty_of_pre_ty out; }

let rec is_static st =
  match st with
  | Sy_scal S_static -> true
  | Sy_scal S_dynamic -> false
  | Sy_prod st_l -> List.exists is_static st_l

let is_static_signature ssig = is_static ssig.input || is_static ssig.output

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

let solve constraints = (* TODO: solve incrementally *)
  let rec solve worklist idle =
    match worklist with
    | [] -> ()
    | c :: worklist ->
      (
        match unalias c.lhs, unalias c.rhs with
        | Psy_var { v_id = v1; }, Psy_var { v_id = v2; } ->
          let idle = add_constr idle c v1 in
          let idle = add_constr idle c v2 in
          solve worklist idle
        | lhs, rhs ->
          let new_work_from_lhs, idle = awake_if_var idle lhs in
          let new_work_from_rhs, idle = awake_if_var idle rhs in
          let worklist = new_work_from_lhs @ new_work_from_rhs @ worklist in
          let worklist, idle = solve_constraint c worklist idle in
          solve worklist idle
      )

  (* D <: S *)
  and solve_constraint c worklist idle =
    match c.lhs, c.rhs with
    (* impossible if called from solve *)
    | Psy_var _, Psy_var _ -> invalid_arg "solve_constraint"

    (*
      rule solved by unification:
      t <: D => t = D,
      S <: t => t = S
    *)
    | _, Psy_scal S_dynamic | Psy_scal S_static, _ ->
      unify c.loc c.lhs c.rhs;
      worklist, idle

    (*
      nothing to solve, just check
    *)
    | Psy_scal _, Psy_scal _ ->
      unify c.loc c.lhs c.rhs;
      worklist, idle

    | Psy_var { v_id = v; }, Psy_scal S_static
    | Psy_scal S_dynamic, Psy_var { v_id = v; } ->
      worklist, add_constr idle c v

    (* Subtyping of products *)
    | Psy_prod ty_l1, Psy_prod ty_l2 ->
      List.map2 (make_constraint c.loc) ty_l1 ty_l2 @ worklist, idle
    | Psy_prod ty_l, ty -> (* not sure if useful! *)
      List.map (fun sub_ty -> make_constraint c.loc sub_ty ty) ty_l @ worklist,
      idle
    | ty, Psy_prod ty_l -> (* not sure if useful! *)
      List.map (make_constraint c.loc ty) ty_l @ worklist, idle
  in
  solve constraints Utils.Int_map.empty
