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

open Acids_static

(** {2 Errors} *)

type error =
  | Non_causal of Ident.t
  | Unimplemented_builtin of Loc.t * Names.longname

exception Error of error

let non_causal id =
  raise (Error (Non_causal id))

let unimplemented_builtin loc ln =
  raise (Error (Unimplemented_builtin (loc, ln)))

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

let float f = const (Ast_misc.Cfloat f)

let tuple v_l = Tuple v_l

let get_const v =
  match v with
  | Const v -> v
  | _ -> ill_typed "get_const"

let get_econstr v = Ast_misc.get_econstr (get_const v)

let get_bool v = Ast_misc.get_bool (get_econstr v)
let get_int v = Ast_misc.get_int (get_econstr v)
let get_float v = Ast_misc.get_float (get_const v)

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

let builtins =
  let int_bin_to_int f v =
    match get_tuple (Lazy.force v) with
    | [l; r] -> int (f (get_int l) (get_int r))
    | _ -> invalid_arg "int_bin_to_int"
  in

  let float_bin_to_float f v =
    match get_tuple (Lazy.force v) with
    | [l; r] -> float (f (get_float l) (get_float r))
    | _ -> invalid_arg "float_bin_to_float"
  in

  [
    "(+)", int_bin_to_int Int.( + );
    "(-)", int_bin_to_int Int.( - );
    "(*)", int_bin_to_int Int.( * );
    "(/)", int_bin_to_int Int.( / );

    "(+.)", float_bin_to_float ( +. );
    "(-.)", float_bin_to_float ( -. );
    "(*.)", float_bin_to_float ( *. );
    "(/.)", float_bin_to_float ( /. );
  ]

exception Found of value

let access_funs_pat p =
  (* TODO: fuse project_pat and compute_pat_access_funs *)

  let project_pat id p value =
    let rec find value p =
      match p.p_desc with
      | P_var id' | P_condvar (id', _) ->
        if Ident.equal id id' then raise (Found value)
      | P_tuple p_l ->
        let v_l = get_tuple value in
        List.iter2 find v_l p_l
      | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
        find value p
      | P_split pt ->
        Ast_misc.iter_upword (find value) (fun _ -> ()) pt
    in
    try
      find value p;
      invalid_arg ("project_pat: could not find " ^ Ident.to_string id)
    with Found value -> value
  in

  let orig_p = p in

  let rec compute_pat_access_funs acc p =
    match p.p_desc with
    | P_var v | P_condvar (v, _) -> (v, project_pat v orig_p) :: acc
    | P_tuple p_l -> List.fold_left compute_pat_access_funs acc p_l
    | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
      compute_pat_access_funs acc p
    | P_split pt ->
      Ast_misc.fold_upword
        (Utils.flip compute_pat_access_funs)
        (fun _ acc -> acc)
        pt
        acc
  in

  compute_pat_access_funs [] p

(** {2 Suspensions, environments and related functions} *)

type thunk =
  {
    name : Ident.t;
    lval : value Lazy.t;
  }

and node_fun = value Lazy.t -> value

and env =
  {
    intf_env : Interface.env;
    external_nodes : node_fun Names.ShortEnv.t Names.ShortEnv.t;
    current_nodes : node_fun Names.ShortEnv.t;
    values : thunk Ident.Env.t;
  }

let reset_env_var env = { env with values = Ident.Env.empty; }

let add_var env var value =
  { env with values = Ident.Env.add var value env.values; }

let find_var env id = Ident.Env.find id env.values

let add_external_node env modn shortn f =
  let open Names in
  let modn_env =
    try ShortEnv.find modn env.external_nodes
    with Not_found -> ShortEnv.empty
  in
  let modn_env = ShortEnv.add shortn f modn_env in
  {
    env with
      external_nodes = ShortEnv.add modn modn_env env.external_nodes;
  }

let add_node env name node =
  { env with current_nodes = Names.ShortEnv.add name node env.current_nodes; }

let find_node loc env ln =
  let open Names in
  match ln.modn with
  | LocalModule -> ShortEnv.find ln.shortn env.current_nodes
  | Module "Pervasives" ->
    (try List.assoc ln.shortn builtins
     with Not_found -> unimplemented_builtin loc ln)
  | Module modn ->
    let mod_env = ShortEnv.find modn env.external_nodes in
    ShortEnv.find ln.shortn mod_env

(** {2 Static evaluation itself} *)

let not_static s =
  invalid_arg (s ^ ": expression cannot be evaluated")

let force thunk =
  try Lazy.force thunk.lval
  with Lazy.Undefined -> non_causal thunk.name

let rec eval_var env v = force (find_var env v)

and eval_clock_exp env ce =
  assert (ce.ce_info#ci_static <> Static_types.S_dynamic);
  match ce.ce_desc with
  | Ce_condvar v ->
    eval_var env v
  | Ce_pword w ->
    let rec find_any pt =
      match pt with
      | Ast_misc.Leaf x -> x
      | Ast_misc.Power (pt, _) -> find_any pt
      | Ast_misc.Concat [] -> assert false
      | Ast_misc.Concat (x :: _) -> find_any x
    in
    eval_static_exp (find_any w.Ast_misc.u) env
  | Ce_equal (ce, se) ->
    let val_ce = eval_clock_exp env ce in
    let val_se = eval_static_exp se env in
    bool (equal_val val_ce val_se)

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
    apply_node env app e

  | E_where (e, block) ->
    let env = add_local_defs env block in
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
  | E_clock_annot (e, _) | E_type_annot (e, _) | E_spec_annot (e, _)
  | E_dom (e, _) | E_buffer (e, _) ->
    eval_exp env e

and eval_static_exp se env =
  assert (se.se_info#pwi_static <> Static_types.S_dynamic);
  let open Acids_scoped.Info in
  match se.se_desc with
  | Se_var v ->
    eval_var env v
  | Se_econstr ec ->
    econstr ec

and add_local_defs env block =
  (* Since equations are mutually recursive, we update the mutable [eval_env]
     after having enriched the environments with other definitions.
     Cycles will be taken care of by Lazy.force.
  *)
  let eval_env = ref env in
  let env = List.fold_left (eval_eq eval_env) env block.b_body in
  eval_env := env;
  env

(* [eval_eq eval_env env eq] enriches [env] with the lazy values for variables
   present in [eq], evaluated into mutable environment [eval_env]. *)
and eval_eq eval_env env eq =
  let get_value =
    let cell = ref None in
    fun () ->
      match !cell with
      | Some value -> value
      | None ->
        let value = eval_exp !eval_env eq.eq_rhs in
        cell := Some value;
        value
  in

  let access = access_funs_pat eq.eq_lhs in
  let mk_thunk (v, f) = { name = v; lval = lazy (f (get_value ())); } in
  List.fold_left (fun env (v, f) -> add_var env v (mk_thunk (v, f))) env access

and node_fun_of_node_def env nd =
  let env = reset_env_var env in
  let access = access_funs_pat nd.n_input in
  fun value ->
    let mk_thunk (v, f) = { name = v; lval = lazy (f (Lazy.force value)); } in
    let env =
      List.fold_left
        (fun env (v, f) -> add_var env v (mk_thunk (v, f)))
        env
        access
    in
    eval_exp env nd.n_body

and apply_node env app e =
  let f = find_node app.a_loc env app.a_op in
  f (lazy (eval_exp env e))

let add_node_def env nd =
  let f = node_fun_of_node_def env nd in
  add_node env nd.n_name f

let make_env intf_env =
  let open Names in

  let empty_env =
    {
      intf_env = intf_env;
      external_nodes = ShortEnv.empty;
      current_nodes = ShortEnv.empty;
      values = Ident.Env.empty;
    }
  in

  let add_intf intf_name intf env =
    let add_node node_name ni env =
      let open Interface in
      match ni with
      | I_static sni ->
        let f = node_fun_of_node_def env sni.sn_body in
        add_external_node env intf_name node_name f
      | I_dynamic _ ->
        env
    in
    ShortEnv.fold add_node intf.Interface.i_nodes env
  in
  ShortEnv.fold add_intf intf_env empty_env
