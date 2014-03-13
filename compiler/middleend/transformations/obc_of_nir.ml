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

type env =
  {
    locals : var_dec Ident.Env.t;
  }

let initial_env nd =
  {
    locals = nd.n_env;
  }

(* {2 AST traversal} *)

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

let node nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  let env = initial_env nd in

  (* Gather buffers *)
  let mem =
    let add name vd mem =
      assert (Ident.equal name vd.v_name);
      match vd.v_data with
      | Ty_buffer (ty, size, _) ->
        make_buffer name ty size vd.v_loc :: mem
      | _ ->
        mem
    in
    Ident.Env.fold add nd.n_env []
  in

  {
    Obc.m_name = Nir_sliced.Info.longname_of_sliced_name nd.n_name;
    Obc.m_mem = mem;
    Obc.m_methods = [];
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
