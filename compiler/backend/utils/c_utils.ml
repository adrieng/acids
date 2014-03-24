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

open C

let longname ln =
  let open Names in
  let modn =
    match ln.modn with
    | LocalModule ->
      Interface.get_current_module_name ()
    | Module modn ->
      modn
  in
  modn ^ "_" ^ ln.shortn

let fun_decl_of_fun_def (f : fdef) =
  {
    d_name = f.f_name;
    d_output = f.f_output;
    d_input = List.map (fun v -> v.v_type) f.f_input;
  }

let ty_int = Scal Data_types.Tys_int

let const_int i =
  {
    c_desc = Const Ast_misc.(Cconstr (Ec_int i));
    c_type = ty_int;
  }

let const_sizeof ty =
  {
    c_desc = Sizeof ty;
    c_type = ty_int;
  }

let lvalue_var_int v =
  {
    l_desc = Var v;
    l_type = ty_int;
  }

let lvalue_deref lv =
  match lv.l_type with
  | Pointer ty ->
    {
      l_desc = Deref lv;
      l_type = ty;
    }
  | _ ->
    invalid_arg "lvalue_deref: expected pointer type"

let exp_const c =
  {
    e_desc = ConstExp c;
    e_type = c.c_type;
  }

let exp_lvalue lv =
  {
    e_desc = Lvalue lv;
    e_type = lv.l_type;
  }

let exp_addrof lv =
  {
    e_desc = AddrOf lv;
    e_type = Pointer lv.l_type;
  }

let exp_void ed =
  {
    e_desc = ed;
    e_type = Void;
  }

let exp_int ed =
  {
    e_desc = ed;
    e_type = ty_int;
  }

let exp_const_int i = exp_const (const_int i)

let exp_var_int v = exp_lvalue (lvalue_var_int v)

let exp_call_void call args = exp_void (Call (call, args))

let exp_op_int opn args = exp_int (Op (opn, args))

let exp_sizeof ty = exp_const (const_sizeof ty)

let make_struct_alloc name =
  let mty = Struct name in
  let mpty = Pointer mty in
  let init =
    {
      e_desc = Call (Backend_utils.alloc, [exp_sizeof mty]);
      e_type = mpty;
    }
  in
  let ret = Ident.make_internal "ret" in
  let ret_lv =
    {
      l_desc = Var ret;
      l_type = mpty;
    }
  in
  {
    f_name = name ^ "_" ^ Backend_utils.create_name;
    f_output = mpty;
    f_input = [];
    f_body =
      {
        b_locals = [{ v_name = ret; v_type = mpty; v_init = Some init; }];
        b_body = [Return (exp_lvalue ret_lv)];
      }
  }

let make_struct_destroy name =
  let mty = Struct name in
  let mpty = Pointer mty in
  let s = Ident.make_internal "s" in
  let s_lv =
    {
      l_desc = Var s;
      l_type = mpty;
    }
  in
  let free =
    {
      e_desc = Call (Backend_utils.free, [exp_lvalue s_lv]);
      e_type = mpty;
    }
  in
  {
    f_name = name ^ "_" ^ Backend_utils.destroy_name;
    f_output = Void;
    f_input = [{ v_name = s; v_type = mpty; v_init = None; }];
    f_body =
      {
        b_locals = [];
        b_body = [C.Exp free];
      }
  }
