(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2013-2014
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

open Nir
open Nir_sliced

(* {2 Environments} *)

let longname_of_node_name (ln, id) =
  let open Names in
  match ln.modn with
  | Module "Pervasives" ->
    ln
  | _ ->
    Nir_sliced.Info.longname_of_sliced_name (ln, id)

type env =
  {
    locals : var_dec Ident.Env.t;
    locals_per_block : var_dec list Utils.Int_map.t;
    mutable insts : Obc.inst list;
  }

let initial_env nd =
  let locals_per_block =
    let add _ vd locals_per_block =
      match vd.v_scope with
      | Scope_context ->
        locals_per_block
      | Scope_internal (Block_id b_id) ->
        let locals_for_block =
          try Utils.Int_map.find b_id locals_per_block
          with Not_found -> []
        in
        Utils.Int_map.add b_id (vd :: locals_for_block) locals_per_block
    in
    Ident.Env.fold add nd.n_env Utils.Int_map.empty
  in
  {
    locals = nd.n_env;
    locals_per_block = locals_per_block;
    insts = [];
  }

let find_var env id = Ident.Env.find id env.locals

let find_locals_per_block env (Block_id b_id) =
  try Utils.Int_map.find b_id env.locals_per_block
  with Not_found -> []

let new_pword env pw =
  let w = Ident.make_internal "w" in
  env.insts <- { Obc.i_name = w; Obc.i_kind = Obc.Pword pw; } :: env.insts;
  w

let new_mach env ln =
  let m = Ident.make_internal "m" in
  env.insts <- { Obc.i_name = m; Obc.i_kind = Obc.Mach ln; } :: env.insts;
  m

let get_insts env = env.insts

(* {2 Helper functions} *)

let obc_ty_of_nir_ty ty =
  match ty with
  | Ty_var _ -> invalid_arg "obc_ty_of_nir_ty: variable type"
  | Ty_scal tys -> Obc.Ty_scal tys
  | Ty_boxed -> Obc.Ty_boxed
  | Ty_clock -> invalid_arg "obc_ty_of_nir_ty: clock"
  | Ty_buffer _ -> invalid_arg "obc_ty_of_nir_ty: buffer"

let make_buffer name ty size loc =
  {
    Obc.b_name = name;
    Obc.b_type = obc_ty_of_nir_ty ty;
    Obc.b_size = size;
    Obc.b_loc = loc;
  }

let obc_var_dec_of_nir_var_dec vd =
  {
    Obc.v_name = vd.v_name;
    Obc.v_type = obc_ty_of_nir_ty vd.v_data;
    Obc.v_loc = vd.v_loc;
  }

let var_dec_of_var env id =
  let vd = find_var env id in
  assert (id = vd.v_name);
  obc_var_dec_of_nir_var_dec vd

let locals_per_block env b_id =
  List.map obc_var_dec_of_nir_var_dec (find_locals_per_block env b_id)

(* {2 AST traversal} *)

let rec equation env eq =
  match eq.eq_desc with
  | Var (x, y) ->
    Obc.Affect (Obc.Var x, Obc.Lvalue (Obc.Var y))

  | Const (x, c) ->
    Obc.Affect (Obc.Var x, Obc.Const c)

  | Pword (x, pw) ->
    let w = new_pword env pw in
    Obc.Call
      {
        Obc.c_kind = Obc.Pword w;
        Obc.c_inputs = [];
        Obc.c_outputs = [Obc.Var x];
      }

  | Call ([x], { c_op = Box; }, y_l) ->
    let e_l = List.map (fun y -> Obc.Lvalue (Obc.Var y)) y_l in
    Obc.Affect (Obc.Var x, Obc.Box e_l)

  | Call ([x], { c_op = Unbox; }, [y]) ->
    Obc.Affect (Obc.Var x, Obc.Unbox (Obc.Lvalue (Obc.Var y)))

  | Call ([], { c_op = BufferAccess (b, Push, _); }, [y]) ->
    (* TODO *)
    let w = Obc.Const (Ast_misc.(Cconstr (Ec_int Int.one))) in
    Obc.Push (b, w, Obc.Lvalue (Obc.Var y))

  | Call ([x], { c_op = BufferAccess (b, Pop, _); }, []) ->
    (* TODO *)
    let w = Obc.Const (Ast_misc.(Cconstr (Ec_int Int.one))) in
    Obc.Affect (Obc.Var x, Obc.Pop (b, w))

  | Call (x_l, { c_op = Node (ln, i); }, y_l) ->
    let kind =
      let open Names in
      match ln.modn with
      | Module "Pervasives" ->
        Obc.Builtin ln.shortn
      | _ ->
        let m = new_mach env (longname_of_node_name (ln, i)) in
        Obc.Method (Obc.Step, m)
    in
    Obc.Call
      {
        Obc.c_kind = kind;
        Obc.c_inputs = List.map (fun y -> Obc.Lvalue (Obc.Var y)) y_l;
        Obc.c_outputs = List.map (fun x -> Obc.Var x) x_l;
      }

  | Call _ ->
    invalid_arg "equation: bad call"

  | Merge (x, y, c_l) ->
    let case (ec, z) =
      ec, Obc.Affect (Obc.Var x, Obc.Lvalue (Obc.Var z))
    in
    Obc.Switch (Obc.Lvalue (Obc.Var y), List.map case c_l)

  | Split (x_l, y, z, ec_l) ->
    let case x ec =
      ec, Obc.Affect (Obc.Var x, Obc.Lvalue (Obc.Var y))
    in
    Obc.Switch (Obc.Lvalue (Obc.Var z), List.map2 case x_l ec_l)

  | Buffer _ ->
    invalid_arg "equation: buffer"

  | Delay _ ->
    Obc.Skip

  | Block bl ->
    Obc.Block (block env bl)

and block env block =
  {
    Obc.b_locals = locals_per_block env block.b_id;
    Obc.b_body = List.map (equation env) block.b_body;
  }

let node nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  let env = initial_env nd in

  (* Gather buffers *)
  let mem =
    let add name vd mem =
      assert (Ident.equal name vd.v_name);
      match vd.v_data, vd.v_scope with
      | Ty_buffer (ty, size, _), Scope_context ->
        make_buffer name ty size vd.v_loc :: mem
      | _ ->
        mem
    in
    Ident.Env.fold add nd.n_env []
  in

  let step =
    {
      Obc.m_kind = Obc.Step;
      Obc.m_inputs = List.map (var_dec_of_var env) nd.n_input;
      Obc.m_outputs = List.map (var_dec_of_var env) nd.n_output;
      Obc.m_body = block env nd.n_body;
    }
  in

  let reset =
    {
      Obc.m_kind = Obc.Reset;
      Obc.m_inputs = [];
      Obc.m_outputs = [];
      Obc.m_body =
        {
          Obc.b_locals = [];
          Obc.b_body = List.map (fun vd -> Obc.Reset vd.Obc.b_name) mem
        }
    }
  in

  {
    Obc.m_name = longname_of_node_name nd.n_name;
    Obc.m_mem = mem;
    Obc.m_insts = get_insts env;
    Obc.m_methods = [reset; step];
  }

(* {2 Putting it all together} *)

let file ctx (f : Interface.env Nir_sliced.file) =
  ctx,
  {
    Obc.f_name = f.f_name;
    Obc.f_type_defs = f.f_type_defs;
    Obc.f_machines = List.map node f.f_body;
  }

let pass = Backend_utils.make_transform "obc_of_nir" file
