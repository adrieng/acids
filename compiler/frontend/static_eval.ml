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

open Acids_preclock

(** {2 Errors} *)

type error =
  | Non_causal of Ident.t

exception Eval_error of error

let print_error fmt err =
  match err with
  | Non_causal id ->
    Format.fprintf fmt "Variable %a has been defined in terms of itself"
      Ident.print id

let non_causal id =
  raise (Eval_error (Non_causal id))

(** {2 Values and related functions} *)

type value =
  | Const of Ast_misc.const
  | Tuple of value list

let equal_val v1 v2 = v1 = v2

let ill_typed str = invalid_arg (str ^ ": ill-typed")

let const c = Const c

let econstr ec = const (Ast_misc.Cconstr ec)

let bool b = econstr (Ast_misc.Ec_bool b)

let int i = econstr (Ast_misc.Ec_int i)

let tuple v_l = Tuple v_l

let get_econstr v =
  match v with
  | Const (Ast_misc.Cconstr ec) -> ec
  | _ -> ill_typed "get_econstr"

let get_bool v =
  let open Ast_misc in
  match v with
  | Const (Cconstr (Ec_bool b)) -> b
  | _ -> ill_typed "get_bool"

let get_int v =
  let open Ast_misc in
  match v with
  | Const (Cconstr (Ec_int i)) -> i
  | _ -> ill_typed "get_int"

let get_tuple v =
  match v with
  | Tuple v_l -> v_l
  | _ -> ill_typed "get_tuple"

let val_fst v =
  match v with
  | Tuple [v; _] -> v
  | _ -> ill_typed "value_fst"

let val_snd v =
  match v with
  | Tuple [_; v] -> v
  | _ -> ill_typed "value_fst"

exception Found of value

let project_pat id p value =
  let rec find value p =
    match p.p_desc with
    | P_var (id', _) ->
      if Ident.equal id id' then raise (Found value)
    | P_tuple p_l ->
      let v_l = get_tuple value in
      List.iter2 find v_l p_l
    | P_clock_annot (p, _) | P_type_annot (p, _) ->
      find value p
    | P_split pt ->
      Ast_misc.iter_upword (find value) (fun _ -> ()) pt
  in
  try find value p; None with Found value -> Some value

(** {2 Suspensions, environments and related functions} *)

type thunk =
  {
    name : Ident.t;
    lval : value Lazy.t;
  }

and env =
  {
    intf_env : Interface.env;
    current_nodes : node_def Names.ShortEnv.t;
    values : thunk Ident.Env.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    current_nodes = Names.ShortEnv.empty;
    values = Ident.Env.empty;
  }

let reset_env env = { env with values = Ident.Env.empty; }

let find_thunk env id = Ident.Env.find id env.values

let find_node env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ShortEnv.find ln.shortn env.current_nodes
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    let ni = Interface.find_node intf ln.shortn in
    Interface.node_definition_of_node_item ni

(** {2 Static evaluation itself} *)

let not_static s =
  invalid_arg (s ^ ": expression cannot be evaluated")

let rec force thunk =
  try Lazy.force thunk.lval
  with Lazy.Undefined -> non_causal thunk.name

and eval_var env v = force (find_thunk env v)

and eval_clock_exp env ce =
  assert (ce.ce_info#ci_static <> Static_types.S_dynamic);
  match ce.ce_desc with
  | Ce_var v ->
    eval_var env v
  | Ce_pword w ->
    let rec find_any pt =
      match pt with
      | Ast_misc.Leaf x -> x
      | Ast_misc.Power (pt, _) -> find_any pt
      | Ast_misc.Concat [] -> assert false
      | Ast_misc.Concat (x :: _) -> find_any x
    in
    eval_pword_exp (find_any w.Ast_misc.u) env
  | Ce_equal (ce, e) ->
    let val_ce = eval_clock_exp env ce in
    let val_e = eval_exp env e in
    bool (equal_val val_ce val_e)
  | Ce_iter _ ->
    not_static "eval_static_clock_exp"

and eval_exp env e =
  assert (e.e_info#ei_static
          <> Static_types.Sy_scal Static_types.S_dynamic);
  match e.e_desc with
  | E_var v ->
    eval_var env v

  | E_const c ->
    const c

  | E_fst e ->
    val_fst (eval_exp env e)

  | E_snd e ->
    val_snd (eval_exp env e)

  | E_tuple e_l ->
    tuple (List.map (eval_exp env) e_l)

  | E_fby _ ->
    not_static "eval_exp"

  | E_ifthenelse (e1, e2, e3) ->
    let v = eval_exp env e1 in
    eval_exp env (if get_bool v then e2 else e3)

  | E_app (app, e) ->
    let v = eval_exp env e in
    let nd = find_node env app.a_op in
    apply_node env nd v

  | E_where (e, block) ->
    let env = eval_block env block in
    eval_exp env e

  | E_bmerge (ce, e1, e2) ->
    let v = eval_clock_exp env ce in
    eval_exp env (if get_bool v then e1 else e2)

  | E_merge (ce, c_l) ->
    let v = eval_clock_exp env ce in
    let ec = get_econstr v in
    let c = List.find (fun c -> c.c_sel = ec) c_l in
    eval_exp env c.c_body

  | E_valof ce ->
    eval_clock_exp env ce

  | E_when (e, _) | E_split (_, e, _)
  | E_clock_annot (e, _) | E_type_annot (e, _)
  | E_dom (e, _) | E_buffer e ->
    eval_exp env e

and eval_pword_exp pwe env =
  assert (pwe.pwe_info#pwi_static <> Static_types.S_dynamic);
  match pwe.pwe_desc with
  | Pwe_var v ->
    eval_var env v
  | Pwe_econstr ec ->
    econstr ec
  | Pwe_fword ec_l ->
    int (List.hd ec_l)

and eval_block env block =
  assert false

and apply_node env nd value =
  assert false

let eval_file ctx (file : < interfaces : Interface.env > Acids_preclock.file) =
  ctx, file

(** {2 Putting it all together} *)

let eval =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_preclock.print_file
       "static_eval"
       eval_file)
