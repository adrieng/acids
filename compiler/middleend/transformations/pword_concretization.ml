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

(* The goal of this pass is to remove the Ce_pword constructors from clock
   expressions (Nir module) and stream types (Clock_types module). Each one is
   replaced with a fresh name properly annotated with the corresponding Spec.

   The pass maintains an environmnet mapping a given pword (on a certain base
   clock) to a variable name. When it sees this pword again, it replaces it with
   a reference to the given variable.

   Since some variables may already be tagged with pword specs, we walk the
   variable declarations to create the initial environment.
*)

open Nir

module PwordEnv =
  Utils.MakeMap(
    struct
      type t = Nir.clock * Pword.pword
      let compare ((ck1 : Nir.clock), p1) (ck2, p2) =
        let i = Nir_utils.clock_compare ck1 ck2 in
        Utils.compare_both i (fun () -> Pword.pword_compare p1 p2)
    end
  )

let pword_var_prefix = "p"

let get_pword_generator () =
  List.assoc
    !Compiler_options.pword_generator
    Pword_generators.available_generators

(** {2 Environment} *)

type env =
  {
    senv : Nir_utils.signature_env;
    current_vars : unit var_dec Ident.Env.t;
    current_pwords : Ident.t PwordEnv.t;
    new_eqs : Ident.t eq list;
    current_scope : scope;
  }

let initial_env file =
  {
    senv = Nir_utils.signature_env_of_file file;
    current_vars = Ident.Env.empty;
    current_pwords = PwordEnv.empty;
    new_eqs = [];
    current_scope = Scope_internal (Block_id 0);
  }

let add_pword env p ck x =
  { env with current_pwords = PwordEnv.add (ck, p) x env.current_pwords; }

let find_or_add_pword env p ck =
  try env, PwordEnv.find (ck, p) env.current_pwords
  with Not_found ->
    let x = Ident.make_internal pword_var_prefix in
    let x_vd =
      Nir_utils.make_var
        x
        (Ty_scal Data_types.Tys_int)
        ck
        env.current_scope
        [Ann_spec (Ast_misc.Word (Pword.to_tree_pword p))]
    in

    let new_eqs, current_vars =
      get_pword_generator
        ()
        env.current_scope
        p
        x
        (env.new_eqs, Ident.Env.add x x_vd env.current_vars)
    in

    add_pword
      {
        env with
          current_vars = current_vars;
          new_eqs = new_eqs;
      }
      p
      ck
      x,
    x

let enter_block env block =
  {
    env with
      new_eqs = [];
      current_scope = Scope_internal block.b_id;
  }

let leave_block local_env enclosing_env =
  {
    enclosing_env with
      current_vars = local_env.current_vars;
      current_pwords = local_env.current_pwords;
  }

(** {2 Putting it all together} *)

let rec walk_clock_clock_exp env base_clock ce =
  let open Clock_types in
  match ce with
  | Ce_condvar _ ->
    env, ce
  | Ce_pword p ->
    let p = Clock_types.pword_of_econstr_tree p in
    let env, x = find_or_add_pword env p base_clock
    in
    let cev =
      {
        cecv_name = x;
        cecv_bounds = Pword.bounds p;
        cecv_specs = [Ast_misc.Word (Pword.to_tree_pword p)];
      }
    in
    env, Ce_condvar cev
  | Ce_equal (ce, ec) ->
    let env, ce = walk_clock_clock_exp env base_clock ce in
    env, Ce_equal (ce, ec)

let rec walk_clock_exp env ce =
  match ce.ce_desc with
  | Ce_condvar _ ->
    env, ce
  | Ce_pword p ->
    let p = Clock_types.pword_of_econstr_tree p in
    let env, x = find_or_add_pword env p ce.ce_clock in
    env, { ce with ce_desc = Ce_condvar x; }
  | Ce_equal (ce, ec) ->
    let env, ce = walk_clock_exp env ce in
    env, { ce with ce_desc = Ce_equal (ce, ec); }

let rec walk env eq =
  match eq.eq_desc with
  | Var _
  | Const _
  | Call _
  | Buffer _
  | Delay _
    ->
    env, eq

  | Merge (x, ce, c_l) ->
    let env, ce = walk_clock_exp env ce in
    env, { eq with eq_desc = Merge (x, ce, c_l); }

  | Split (x_l, ce, y, ec_l) ->
    let env, ce = walk_clock_exp env ce in
    env, { eq with eq_desc = Split (x_l, ce, y, ec_l); }

  | Valof (x, ce) ->
    let env, ce = walk_clock_exp env ce in
    env, { eq with eq_desc = Valof (x, ce); }

  | Block block ->
    let env, block = walk_block env block in
    env, { eq with eq_desc = Block block; }

and walk_block env block =
  let local_env = enter_block env block in
  let local_env, body = Utils.mapfold_left walk local_env block.b_body in
  leave_block local_env env, { block with b_body = body; }

let node orig_env nd =
  (* Walk the variable declarations, checking each variable to see if it has
     some pword spec annotation. If it does, add it to the environment. *)
  let env =
    let add_annot _ vd env =
      let open Ast_misc in
      try
        match
          List.find
            (fun ann ->
              match ann with
              | Ann_spec (Word _) -> true
              | _ -> false)
            vd.v_annots
        with
        | Ann_spec (Word p) ->
          add_pword env (Resolution_utils.pword_of_tree p) vd.v_clock vd.v_name
        | _ -> assert false
      with Not_found ->
        env
    in
    Ident.Env.fold
      add_annot
      nd.n_env
      { orig_env with current_vars = nd.n_env; }
  in

  let node_env, body = walk_block env nd.n_body in
  let env = leave_block node_env orig_env in
  {
    nd with
      n_body = { body with b_body = env.new_eqs @ body.b_body; };
      n_env = env.current_vars;
  }

let tr ctx file =
  let env = initial_env file in
  Middleend_utils.map_to_nodes (node env) ctx file

let pass =
  Middleend_utils.(make_transform "pword_concretization" tr)
