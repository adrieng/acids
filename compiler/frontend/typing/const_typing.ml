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

(** {1 Const typing} *)

open Acids_typed
open Const_types

(** Const typing is a very simple (two-element) type system used to distinguish
    which nodes have to be inlined. It drives const evaluation later on. *)

(** {2 Errors} *)

type error =
  | Unification_error of Const_types.error
  | Const_inputs of Names.shortname

exception Typing_error of error

let print_error fmt err =
  match err with
  | Unification_error err ->
    Const_types.print_error fmt err
  | Const_inputs nn ->
    Format.fprintf fmt
      "Node %a has const inputs but has not been declared const"
      Names.print_shortname nn

let unification_error err =
  raise (Typing_error (Unification_error err))

let const_inputs nn =
  raise (Typing_error (Const_inputs nn))

(** {2 Unification} *)

(** {2 Low-level utilities} *)

let reset_ty, fresh_ty =
  let open PreTy in
  let open VarTy in
  let r = ref 0 in
  (fun () -> r := 0),
  (fun () -> incr r; Psy_var { v_link = None; v_id = !r; })

exception Non_constant_pword

(* A tree pword is constant if all its sub-pwordexps are syntacticaly equal *)
let is_constant_pword get w =
  let check_constant se acc =
    match acc with
    | Some prev_se ->
      if get se <> get prev_se
      then raise Non_constant_pword
      else acc
    | None ->
      Some se
  in
  try
    ignore (Tree_word.fold_upword check_constant (fun _ acc -> acc) w None);
    true
  with Non_constant_pword -> false

(** {2 Typing environments} *)

type typing_env =
  {
    (** maps module names to interfaces *)
    intf_env : Interface.env;
    (** maps constructors from the current module to type names *)
    current_constr : Names.shortname Names.ShortEnv.t;
    (** maps nodes from the current module to type signatures *)
    current_nodes : ty_sig Names.ShortEnv.t;
    (** maps global pwords to boolean true iff they are constant *)
    current_pwords_const : bool Names.ShortEnv.t;
    (** maps current idents to (pre)types *)
    idents : VarTy.t Ident.Env.t;
    (** subtyping constraint system *)
    mutable constr : Const_types.constr list;
  }

let debug_typing_env fmt env =
  Ident.Env.print VarTy.print ";" fmt env.idents

let initial_typing_env info =
  {
    intf_env = info#interfaces;
    current_constr = Names.ShortEnv.empty;
    current_nodes = Names.ShortEnv.empty;
    current_pwords_const = Names.ShortEnv.empty;
    idents = Ident.Env.empty;
    constr = [];
  }

let reset_env env = { env with idents = Ident.Env.empty; constr = []; }

let find_ident env id = Ident.Env.find id env.idents

let add_fresh_type_for_var env id =
  { env with idents = Ident.Env.add id (fresh_ty ()) env.idents; }

let add_constraint env c = env.constr <- c :: env.constr

let find_node_signature env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ShortEnv.find ln.shortn env.current_nodes
  | Module modn ->
    let intf = Names.ShortEnv.find modn env.intf_env in
    let ni = Interface.find_node intf ln.shortn in
    Interface.const_signature_of_node_item ni

let add_local_node_signature env shortn ssig =
  { env with current_nodes = Names.ShortEnv.add shortn ssig env.current_nodes; }

let is_constant_global_pword env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ShortEnv.find ln.shortn env.current_pwords_const
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    let w = Interface.((find_pword intf ln.shortn).pi_value) in
    is_constant_pword (fun x -> x) w

let add_pword env pn w =
  let get se = se.se_desc in
  let current_pwords_const =
    Names.ShortEnv.add pn (is_constant_pword get w) env.current_pwords_const
  in
  { env with current_pwords_const = current_pwords_const; }

let solve_subtyping_constraints env = Const_types.solve env.constr

(** {2 High-level utilities} *)

let const_ty = PreTy.Psy_scal S_const
let nonconst_ty = PreTy.Psy_scal S_nonconst
let tuple_ty ty_l = PreTy.Psy_prod ty_l

module A =
struct
  type new_annot =
  | Exp of VarTy.t
  | Node of bool * VarTy.t * VarTy.t (* is_const * inp * out *)
  | App of bool (* true iff application is const *)

  let print_new_annot fmt na =
    match na with
    | Exp ty -> VarTy.print fmt ty
    | Node (const, ty1, ty2) ->
      Format.fprintf fmt "@[%a@ -{%b}>@ %a@]"
        VarTy.print ty1
        const
        VarTy.print ty2
    | App is_const ->
      Format.fprintf fmt "app is%s const" (if is_const then " not" else "")
end

module ANN_INFO = Acids_utils.MakeAnnot(Acids_typed)(A)
module M = Acids.Make(ANN_INFO)

let annotate_exp e ty = ANN_INFO.annotate e.e_info (A.Exp ty)
let annotate_clock_exp ce ty = ANN_INFO.annotate ce.ce_info (A.Exp ty)
let annotate_const_exp se ty = ANN_INFO.annotate se.se_info (A.Exp ty)
let annotate_pat p ty = ANN_INFO.annotate p.p_info (A.Exp ty)
let annotate_node node inp_ty out_ty =
  ANN_INFO.annotate node.n_info (A.Node (node.n_const, inp_ty, out_ty))
let annotate_app info const = ANN_INFO.annotate info (A.App const)
let annotate_dummy info = ANN_INFO.annotate info (A.Exp const_ty)

module MORPH =
struct
  module IN_INFO = M.I
  module OUT_INFO = Acids_const.Info

  open ANN_INFO
  open A

  let update_clock_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      (
        match ty with
        | Sy_scal tys ->
          object
            method ci_data = info#ci_data
            method ci_const = tys
          end
        | Sy_var _ -> (* default to nonconst *)
          object
            method ci_data = info#ci_data
            method ci_const = S_nonconst
          end
        | _ ->
          invalid_arg "update_clock_exp_info"
      )

  let update_const_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ -> invalid_arg "update_const_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      (
        match ty with
        | Sy_scal tys ->
          object
            method pwi_data = info#pwi_data
            method pwi_const = tys
          end
        | _ -> invalid_arg "update_const_exp_info"
      )

  let update_exp_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      object
        method ei_data = info#ei_data
        method ei_const = ty
      end

  let update_app_info { new_annot = na; _ } =
    match na with
    | Exp _ | Node _ -> invalid_arg "update_app_info"
    | App is_const -> { Acids_const.Info.ai_is_const = is_const; }

  let update_block_info _ = ()

  let update_pat_info { new_annot = na; old_annot = info; } =
    match na with
    | Node _ | App _ -> invalid_arg "update_clock_exp_info"
    | Exp pty ->
      let ty = ty_of_pre_ty pty in
      object
        method pi_data = info#pi_data
        method pi_const = ty
      end

  let update_eq_info _ = ()

  let update_domain_info _ = ()

  let update_buffer_info _ = ()

  let update_node_info  { new_annot = na; old_annot = info; } =
    match na with
    | Exp _ | App _ -> invalid_arg "update_node_info"
    | Node (const, inp, out) ->
      object
        method ni_ctx = info#ni_ctx
        method ni_data = info#ni_data
        method ni_const = generalize_sig const inp out
      end
end
module EXTRACT = Acids_utils.MakeMap(M)(Acids_const)(MORPH)

let exp_type e = e.M.e_info.ANN_INFO.new_annot

(** {2 Utility functions} *)

let rec enrich_pat env p =
  match p.p_desc with
  | P_var v ->
    add_fresh_type_for_var env v
  | P_tuple p_l ->
    List.fold_left enrich_pat env p_l
  | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
    enrich_pat env p
  | P_split pt ->
    Tree_word.fold_upword
      (fun p env -> enrich_pat env p)
      (fun _ env -> env)
      pt
      env

let check_and_transform_non_const_sig name ssig =
  let open Const_types in

  if Const_types.is_const ssig.input then const_inputs name;

  let rec remap_to_nonconst st =
    match st with
    | Sy_var _ | Sy_scal _ -> Sy_scal S_nonconst
    | Sy_prod ty_l -> Sy_prod (List.map remap_to_nonconst ty_l)
  in

  {
    input = remap_to_nonconst ssig.input;
    output = remap_to_nonconst ssig.output;
    const = S_nonconst;
  }

(** {2 Typing AST nodes} *)

let rec type_clock_exp env ce =
  let ced, ty =
    match ce.ce_desc with
    | Ce_condvar id ->
      M.Ce_condvar id, find_ident env id

    | Ce_pword (Pd_lit pw) ->
      let pw, ty = type_const_word env pw in
      M.Ce_pword (M.Pd_lit pw), ty

    | Ce_pword (Pd_global ln) ->
      M.Ce_pword (M.Pd_global ln),
      if is_constant_global_pword env ln then const_ty else nonconst_ty

    | Ce_equal (ce, se) ->
      let ce, ty = type_clock_exp env ce in
      let se = type_const_exp env se in
      M.Ce_equal (ce, se), ty
  in
  {
    M.ce_desc = ced;
    M.ce_loc = ce.ce_loc;
    M.ce_info = annotate_clock_exp ce ty;
  },
  ty

and type_const_word env pw =
  let type_fun = type_const_exp env in
  let ty =
    let get se = se.se_desc in
    if is_constant_pword get pw then const_ty else nonconst_ty
  in
  Tree_word.map_upword type_fun type_fun pw, ty

and type_const_exp env se =
  let open Acids_scoped.Info in
  let sed, ty =
    match se.se_desc with
    | Se_var v ->
      let ty = find_ident env v in
      unify se.se_loc const_ty ty;
      Se_var v, ty
    | Se_global ln ->
      Se_global ln, const_ty
    | Se_econstr ec ->
      Se_econstr ec, const_ty
    | Se_binop (op, se1, se2) ->
      let se1 = type_const_exp env se1 in
      let se2 = type_const_exp env se2 in
      Se_binop (op, se1, se2), const_ty
  in
  {
    M.se_desc = sed;
    M.se_loc = se.se_loc;
    M.se_info = annotate_const_exp se ty;
  }

and type_exp env e =
  let loc = e.e_loc in
  let ed, ty =
    match e.e_desc with
    | E_var v ->
      M.E_var v, find_ident env v

    | E_const c ->
      M.E_const c, const_ty

    | E_fst e ->
      let ty_l = fresh_ty () in
      let ty_r = fresh_ty () in
      let e = expect_exp loc env (tuple_ty [ty_l; ty_r]) e in
      M.E_fst e, ty_l

    | E_snd e ->
      let ty_l = fresh_ty () in
      let ty_r = fresh_ty () in
      let e = expect_exp loc env (tuple_ty [ty_l; ty_r]) e in
      M.E_snd e, ty_r

    | E_tuple e_l ->
      let ety_l = List.map (type_exp env) e_l in
      let e_l, ty_l = List.split ety_l in
      M.E_tuple e_l, tuple_ty ty_l

    | E_fby (e1, e2) ->
      let e1, _ = type_exp env e1 in
      let e2, _ = type_exp env e2 in
      M.E_fby (e1, e2), nonconst_ty

    | E_ifthenelse (e1, e2, e3) ->
      let e1, ty = type_exp env e1 in
      let e2 = expect_exp loc env ty e2 in
      let e3 = expect_exp loc env ty e3 in
      M.E_ifthenelse (e1, e2, e3), ty

    | E_app (app, e) ->
      let ssig = find_node_signature env app.a_op in
      let app =
        {
          M.a_op = app.a_op;
          M.a_loc = app.a_loc;
          M.a_info =
            annotate_app app.a_info (Const_types.is_const_signature ssig);
        }
      in
      let inp, out = Const_types.instantiate_ty_sig fresh_ty ssig in
      let e = expect_exp loc env inp e in
      M.E_app (app, e), out

    | E_where (e, block) ->
      let block, new_env = type_block env block in
      let e, ty = type_exp new_env e in

      (* /!\ since we are dropping new_env, update the current list of
         constraints with those gathered from the block /!\ *)
      env.constr <- new_env.constr;

      M.E_where (e, block), ty

    | E_when (e, ce) ->
      let e, ty = type_exp env e in
      let ce, _ = type_clock_exp env ce in
      M.E_when (e, ce), ty

    | E_split (ce, e, ec_l) ->
      let ce, _ = type_clock_exp env ce in
      let e, ty = type_exp env e in
      M.E_split (ce, e, ec_l), ty

    | E_bmerge (ce, e1, e2) ->
      let ce, ty = type_clock_exp env ce in
      let e1 = expect_exp loc env ty e1 in
      let e2 = expect_exp loc env ty e2 in
      M.E_bmerge (ce, e1, e2), ty

    | E_merge (ce, c_l) ->
      let ce, ty = type_clock_exp env ce in
      let c_l =
        List.map
          (fun ec ->
            let e = expect_exp loc env ty ec.c_body in
            {
              M.c_sel = ec.c_sel;
              M.c_body = e;
              M.c_loc = ec.c_loc;
            })
          c_l
      in
      M.E_merge (ce, c_l), ty

    | E_valof ce ->
      let ce, ty = type_clock_exp env ce in
      M.E_valof ce, ty

    | E_clock_annot (e, cka) ->
      let e, ty = type_exp env e in
      let cka = type_clock_annot env cka in
      M.E_clock_annot (e, cka), ty

    | E_type_annot (e, ta) ->
      let e, ty = type_exp env e in
      M.E_type_annot (e, ta), ty

    | E_spec_annot (e, spec) ->
      let spec = type_spec env spec in
      let e, ty = type_exp env e in
      M.E_spec_annot (e, spec), ty

    | E_dom (e, dom) ->
      let e, ty = type_exp env e in
      let dom = type_domain env dom in
      M.E_dom (e, dom), ty

    | E_buffer (e, bu) ->
      let e, ty = type_exp env e in
      let bu = type_buffer env bu in
      M.E_buffer (e,  bu), ty

  in
  {
    M.e_desc = ed;
    M.e_loc = e.e_loc;
    M.e_info = annotate_exp e ty;
  },
  ty

and expect_clock_exp loc env expected_ty ce =
  let ce, actual_ty = type_clock_exp env ce in
  add_constraint env (Const_types.make_constraint loc actual_ty expected_ty);
  ce

and expect_exp loc env expected_ty e =
  let e, actual_ty = type_exp env e in
  add_constraint env (Const_types.make_constraint loc actual_ty expected_ty);
  e

and type_merge_clause env c =
  let body, ty = type_exp env c.c_body in
  {
    M.c_sel = c.c_sel;
    M.c_body = body;
    M.c_loc = c.c_loc;
  },
  ty

and type_clock_annot env cka =
  match cka with
  | Ca_var i -> M.Ca_var i
  | Ca_on (cka, ce) ->
    let cka = type_clock_annot env cka in
    let ce, _ = type_clock_exp env ce in
    M.Ca_on (cka, ce)

and type_domain env dom =
  {
    M.d_base_clock = Utils.map_opt (type_clock_annot env) dom.d_base_clock;
    M.d_par = dom.d_par;
    M.d_info = annotate_dummy dom.d_info;
  }

and type_buffer _ bu =
  {
    M.bu_info = annotate_dummy bu.bu_info;
  }

and type_pat env p =
  let loc = p.p_loc in
  let pd, ty =
    match p.p_desc with
    | P_var id ->
      M.P_var id, find_ident env id
    (* | P_condvar (id, specs) -> *)
    (*   let specs = List.map (type_spec env) specs in *)
    (*   M.P_condvar (id, specs), find_ident env id *)
    | P_tuple p_l ->
      let pty_l = List.map (type_pat env) p_l in
      let p_l, ty_l = List.split pty_l in
      M.P_tuple p_l, tuple_ty ty_l
    | P_clock_annot (p, cka) ->
      let p, ty = type_pat env p in
      let cka = type_clock_annot env cka in
      M.P_clock_annot (p, cka), ty
    | P_type_annot (p, tya) ->
      let p, ty = type_pat env p in
      M.P_type_annot (p, tya), ty
    | P_spec_annot (p, spec) ->
      let p, ty = type_pat env p in
      let spec = type_spec env spec in
      M.P_spec_annot (p, spec), ty
    | P_split pt ->
      let ty = fresh_ty () in
      let pt =
        Tree_word.map_upword (expect_pat loc env ty) (type_const_exp env) pt
      in
      M.P_split pt, ty
  in
  {
    M.p_desc = pd;
    M.p_loc = loc;
    M.p_info = annotate_pat p ty;
  },
  ty

and expect_pat loc env expected_ty p =
  let p, actual_ty = type_pat env p in
  add_constraint env (Const_types.make_constraint loc actual_ty expected_ty);
  p

and type_eq env eq =
  (* Note that the type of e should be a sub-type of p, not the converse *)
  let desc =
    match eq.eq_desc with
    | Eq_plain (lhs, rhs) ->
      let lhs, ty = type_pat env lhs in
      let rhs = expect_exp eq.eq_loc env ty rhs in
      M.Eq_plain (lhs, rhs)
    | Eq_condvar (lhs, specs, rhs) ->
      let specs = List.map (type_spec env) specs in
      let ty = find_ident env lhs in
      M.Eq_condvar (lhs, specs, expect_exp eq.eq_loc env ty rhs)
  in
  {
    M.eq_desc = desc;
    M.eq_loc = eq.eq_loc;
    M.eq_info = annotate_dummy eq.eq_info;
  }

and type_block env block =
  let new_env =
    let enrich env eq =
      match eq.eq_desc with
      | Eq_plain (lhs, _) -> enrich_pat env lhs
      | Eq_condvar (lhs, _, _) -> add_fresh_type_for_var env lhs
    in
    List.fold_left enrich env block.b_body
  in

  let body = List.map (type_eq new_env) block.b_body in

  {
    M.b_body = body;
    M.b_info = annotate_dummy block.b_info;
    M.b_loc = block.b_loc;
  },
  new_env

and type_spec env spec =
  let sd =
    match spec.s_desc with
    | Unspec -> M.Unspec
    | Word w ->
      let type_fun = type_const_exp env in
      let w = Tree_word.map_upword type_fun type_fun w in
      M.Word w
    | Interval (l, u) ->
      let l = type_const_exp env l in
      let u = type_const_exp env u in
      M.Interval (l, u)
  in
  {
    M.s_desc = sd;
    M.s_loc = spec.s_loc;
  }

let type_node_def env nd =
  let env = reset_env env in
  let env = enrich_pat env nd.n_input in

  let input, inp_ty = type_pat env nd.n_input in
  let out_ty = if nd.n_const then const_ty else fresh_ty () in
  let body = expect_exp nd.n_loc env out_ty nd.n_body in

  (* TODO solve incrementally at where level *)
  solve_subtyping_constraints env;

  let ssig = generalize_sig nd.n_const inp_ty out_ty in

  (* non-const nodes may not have const inputs, and only have nonconst outputs,
     see the relevant section of the manual *)
  let ssig =
    if nd.n_const
    then ssig
    else check_and_transform_non_const_sig nd.n_name ssig
  in

  {
    M.n_name = nd.n_name;
    M.n_input = input;
    M.n_body = body;
    M.n_pragma = nd.n_pragma;
    M.n_const = nd.n_const;
    M.n_loc = nd.n_loc;
    M.n_info = annotate_node nd inp_ty out_ty;
  },
  add_local_node_signature env nd.n_name ssig

let type_node_decl env nd =
  {
    M.decl_name = nd.decl_name;
    M.decl_data = nd.decl_data;
    M.decl_const = nd.decl_const;
    M.decl_clock = nd.decl_clock;
    M.decl_loc = nd.decl_loc;
  },
  add_local_node_signature env nd.decl_name nd.decl_const

let type_type_def env td =
  {
    M.ty_name = td.ty_name;
    M.ty_body = td.ty_body;
    M.ty_loc = td.ty_loc;
  },
  env

let type_const_def env sd =
  let body = expect_exp sd.sd_loc env const_ty sd.sd_body in
  {
    M.sd_name = sd.sd_name;
    M.sd_body = body;
    M.sd_loc = sd.sd_loc;
  },
  env

let type_pword_def env pd =
  let body, _ = type_const_word env pd.pd_body in
  {
    M.pd_name = pd.pd_name;
    M.pd_body = body;
    M.pd_loc = pd.pd_loc;
  },
  add_pword env pd.pd_name pd.pd_body

let type_phrase env phr =
  match phr with
  | Phr_node_def nd ->
    let nd, env = type_node_def env nd in
    env, M.Phr_node_def nd
  | Phr_node_decl nd ->
    let nd, env = type_node_decl env nd in
    env, M.Phr_node_decl nd
  | Phr_type_def td ->
    let td, env = type_type_def env td in
    env, M.Phr_type_def td
  | Phr_const_def sd ->
    let sd, env = type_const_def env sd in
    env, M.Phr_const_def sd
  | Phr_pword_def pd ->
    let pd, env = type_pword_def env pd in
    env, M.Phr_pword_def pd

let type_file file =
  try
    let env = initial_typing_env file.f_info in
    let _, body = Utils.mapfold_left type_phrase env file.f_body in
    {
      M.f_name = file.f_name;
      M.f_imports = file.f_imports;
      M.f_info = file.f_info;
      M.f_body = body;
    }
  with Const_types.Unification_error err ->
    unification_error err

(** {2 Moving from pretypes to types} *)

let type_file
    ctx
    (file
       : < interfaces : Interface.env > Acids_typed.file) =
  let intermediate_file = type_file file in
  let final_file = EXTRACT.extract_file intermediate_file in
  ctx, final_file

(** {2 Putting it all together} *)

let pass =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_const.print_file
       "const_typing"
       type_file)
