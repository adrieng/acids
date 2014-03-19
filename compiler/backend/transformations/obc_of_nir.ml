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
open Backend_utils

(*
  TODO: document runtime system

  pword : prefix_size * total_size * data * lengthes

*)

let mk_const ec = Obc.C_scal (Ast_misc.(Cconstr ec))

let mk_int (* TODO factor in Ast_misc *) i = mk_const (Ast_misc.Ec_int i)

let builtin_machine_ty =
  {
    Obc.mt_name = runtime builtin_name;
    Obc.mt_cparams = [];
  }

let pword_machine_ty pw =
  let prefix_size, p = Tree_word.pair_list_of_pword_int pw in
  let p_dat, p_len = List.split p in
  {
    Obc.mt_name = runtime pword_name;
    Obc.mt_cparams =
      [
        mk_int prefix_size;
        mk_int (Int.of_int (List.length p_len));
        Obc.C_array (List.map mk_const p_dat);
        Obc.C_array (List.map mk_int p_len);
      ];
  }

let buffer_machine_ty ty capacity =
  {
    Obc.mt_name = runtime buffer_name;
    Obc.mt_cparams =
      [
        Obc.C_sizeof ty;
        mk_int capacity;
      ];
  }

let boxed_machine_ty =
  {
    Obc.mt_name = runtime boxed_name;
    Obc.mt_cparams = [];
  }

let rec translate_ty ty =
  match ty with
  | Ty_boxed ->
    Obc.Ty_mach boxed_machine_ty
  | Ty_scal tys ->
    Obc.Ty_scal tys
  | Ty_buffer (ty, capacity, _) ->
    Obc.Ty_mach (buffer_machine_ty (translate_ty ty) capacity)

let translate_var_dec vd =
  let ty = translate_ty vd.v_data in
  let ty =
    match ty with
    | Obc.Ty_scal _ ->
      let mb = Clock_types.max_burst_stream_type vd.v_clock in
      if mb = Int.one then ty else Obc.Ty_arr (ty, mb)
    | _ ->
      ty
  in
  {
    Obc.v_name = vd.v_name;
    Obc.v_type = ty;
    Obc.v_loc = vd.v_loc;
  }

(******************************************************************************)
(* {2 Environments} *)

let longname_of_node_name (ln, id) =
  let open Names in
  match ln.modn with
  | Module "Pervasives" ->
    ln
  | _ ->
    Nir_sliced.Info.longname_of_sliced_name (ln, id)

(* Environment used to translate a given node *)
type env =
  {
    mutable current_blocks : block_id list;

    mutable all : Obc.var_dec Ident.Env.t;
    mutable fields : Obc.var_dec Ident.Env.t;
    mutable locals_per_block : Obc.var_dec list Utils.Int_map.t;

    node_inputs : Ident.Set.t;
    node_outputs : Ident.Set.t;
  }

let debug_env ?(msg = "") env =
  Format.eprintf "@[Env [%s],@ all: {@[%a@]}@ fields: {@[%a@]}@."
    msg
    (Ident.Env.print Obc_printer.print_var_dec ",") env.all
    (Ident.Env.print Obc_printer.print_var_dec ",") env.fields

let push_new_block env b_id =
  env.current_blocks <- b_id :: env.current_blocks

let pop_block env =
  env.current_blocks <- List.tl env.current_blocks

let current_block env = List.hd env.current_blocks

let add_all env vd =
  env.all <- Ident.Env.add vd.Obc.v_name vd env.all

let add_field env vd =
  add_all env vd;
  env.fields <- Ident.Env.add vd.Obc.v_name vd env.fields

let add_local_for_block env (Block_id b_id) vd =
  add_all env vd;
  let locals_for_block =
    try Utils.Int_map.find b_id env.locals_per_block with Not_found -> []
  in
  env.locals_per_block <-
    Utils.Int_map.add b_id (vd :: locals_for_block) env.locals_per_block

let initial_env nd =
  let set_of_list = List.fold_left (Utils.flip Ident.Set.add) Ident.Set.empty in
  let env =
    {
      current_blocks = [];

      all = Ident.Env.empty;
      fields = Ident.Env.empty;
      locals_per_block = Utils.Int_map.empty;

      node_inputs = set_of_list nd.n_input;
      node_outputs = set_of_list nd.n_output;
    }
  in

  let add _ vd =
    let obc_vd = translate_var_dec vd in
    match vd.v_scope with
    | Scope_context ->
      add_field env obc_vd
    | Scope_input | Scope_output ->
      add_all env obc_vd
    | Scope_internal b_id ->
      add_local_for_block env b_id obc_vd
  in
  Ident.Env.iter add nd.n_env;

  env

let add_local_for_current_block env id ty =
  let vd =
    {
      Obc.v_name = id;
      Obc.v_type = ty;
      Obc.v_loc = Loc.dummy;
    }
  in
  env.all <- Ident.Env.add id vd env.all;
  add_local_for_block env (current_block env) vd

let add_local_for_current_block_int env id =
  add_local_for_current_block env id (Obc.Ty_scal Data_types.Tys_int)

let locals_per_block env (Block_id b_id) =
  try Utils.Int_map.find b_id env.locals_per_block
  with Not_found -> []

let find_var env id = Ident.Env.find id env.all

let machine_type_of env x =
  let vd = find_var env x in
  match vd.Obc.v_type with
  | Obc.Ty_mach mty ->
    mty
  | _ ->
    invalid_arg ("machine_type_of: " ^ Ident.to_string x ^ " is not a machine")

let new_pword env pw =
  let w = Ident.make_internal "w" in
  let vd =
    {
      Obc.v_name = w;
      Obc.v_type = Obc.Ty_mach (pword_machine_ty pw);
      Obc.v_loc = Loc.dummy;
    }
  in
  add_field env vd;
  w

let new_node env ln =
  let m = Ident.make_internal "m" in
  let vd =
    {
      Obc.v_name = m;
      Obc.v_type =
        Obc.Ty_mach
          {
            Obc.mt_name = ln;
            Obc.mt_cparams = [];
          };
      Obc.v_loc = Loc.dummy;
    }
  in
  add_field env vd;
  m

let get_fields env =
  Ident.Env.fold (fun _ vd acc -> vd :: acc) env.fields []

let var env id =
  let kind =
    if Ident.Set.mem id env.node_inputs
    then Obc.K_input
    else if Ident.Set.mem id env.node_outputs
    then Obc.K_output
    else if Ident.Env.mem id env.fields
    then Obc.K_field
    else Obc.K_local
  in
  Obc.L_var (kind, id)

let exp_var env id = Obc.E_lval (var env id)

(******************************************************************************)
(* {2 Helper functions} *)

let builtin_op_stm op inputs output =
  Obc.S_call
    {
      Obc.c_inst = None;
      Obc.c_mach = builtin_machine_ty;
      Obc.c_method = Backend_utils.op_name op;
      Obc.c_inputs = inputs;
      Obc.c_outputs = output;
    }

let method_call env inst ?(inputs = []) ?(outputs = []) op  =
  let mty = machine_type_of env inst in
  Obc.S_call
    {
      Obc.c_inst = Some (var env inst);
      Obc.c_mach = mty;
      Obc.c_method = op;
      Obc.c_inputs = inputs;
      Obc.c_outputs = outputs;
    }

let reset_stm env inst mty =
  Obc.S_call
    {
      Obc.c_inst = Some (var env inst);
      Obc.c_mach = mty;
      Obc.c_method = reset_name;
      Obc.c_inputs = [];
      Obc.c_outputs = [];
    }

let step_stm env inst ~inputs ~outputs =
  method_call env inst ~inputs ~outputs step_name

let pword_step_stm env inst out =
  method_call env inst ~outputs:[out] step_name

let buffer_push_stm env inst ~amount ~data =
  method_call env inst ~inputs:[amount; data] push_name

let buffer_pop_stm env inst amount out =
  method_call env inst ~inputs:[amount] ~outputs:[out] pop_name

let reset_if_machine env acc vd =
  let open Obc in
  match vd.v_type with
  | Ty_mach mty ->
    reset_stm env vd.v_name mty :: acc
  | _ ->
    acc

let reset_if_machines env vd_l =
  List.fold_left (reset_if_machine env) [] vd_l

let create_pword env pw out =
  let w = new_pword env pw in
  pword_step_stm env w out

let create_node env ln ~inputs ~outputs =
  let m = new_node env ln in
  step_stm env m ~inputs ~outputs

(* {2 AST traversal} *)

let rec clock_exp env ck_e acc ce =
  let open Clock_types in
  match ce with
  | Ce_condvar cecv ->
    acc, cecv.cecv_name
  | Ce_equal (ce, ec) ->
    let r = Ident.make_internal "r_ce" in
    add_local_for_current_block_int env r;
    let acc, x = clock_exp env ck_e acc ce in
    let open Obc in
    builtin_op_stm ceq_name
      [ck_e; exp_var env x; E_const (mk_const ec)]
      [var env r]
    :: acc,
    r
  | Ce_pword pw ->
    let x = Ident.make_internal "x_w" in
    create_pword env pw (var env x) :: acc, x

and clock_type env acc ck =
  match ck with
  | Clock_types.St_var _ ->
    acc, Obc.E_const (mk_int Int.one)
  | Clock_types.St_on (ck, ce) ->
    let acc, ck_e = clock_type env acc ck in
    let acc, ce_x = clock_exp env ck_e acc ce in
    let ck_x = Ident.make_internal "w" in
    add_local_for_current_block_int env ck_x;
    let ce_e = exp_var env ce_x in
    builtin_op_stm
      "on"
      [ck_e; ce_e]
      [var env ck_x]
    :: acc,
    ce_e

let rec equation env acc eq =
  match eq.eq_desc with
  | Var (x, y) ->
    Obc.S_affect (var env x, exp_var env y) :: acc

  | Const (x, c) ->
    Obc.S_affect (var env x, Obc.E_const (Obc.C_scal c)) :: acc

  | Pword (x, pw) ->
    create_pword env pw (var env x) :: acc

  | Call ([x], { c_op = Box; }, y_l) ->
    builtin_op_stm
      box_name
      (List.map (exp_var env) y_l)
      [var env x]
    :: acc

  | Call (x_l, { c_op = Unbox; }, [y]) ->
    builtin_op_stm
      unbox_name
      [exp_var env y]
      (List.map (var env) x_l)
    :: acc

  | Call ([], { c_op = BufferAccess (b, Push, _); }, [y]) ->
    let acc, w = clock_type env acc eq.eq_base_clock in
    buffer_push_stm env b ~amount:w ~data:(exp_var env y) :: acc

  | Call ([x], { c_op = BufferAccess (b, Pop, _); }, []) ->
    let acc, w = clock_type env acc eq.eq_base_clock in
    buffer_pop_stm env b w (var env x) :: acc

  | Call (x_l, { c_op = Node (ln, i); }, y_l) ->
    let x_l = List.map (var env) x_l in
    let y_l = List.map (exp_var env) y_l in
    let open Names in
    (
      match ln.modn with
      | Module "Pervasives" ->
        builtin_op_stm ln.shortn y_l x_l
      | _ ->
        create_node env (longname_of_node_name (ln, i)) ~outputs:x_l ~inputs:y_l
    )
    :: acc

  | Call _ ->
    invalid_arg "equation: bad call"

  | Merge (x, y, c_l) ->
    let case (ec, z) =
      ec, Obc.(S_affect (var env x, exp_var env z))
    in
    Obc.(S_switch (exp_var env y, List.map case c_l)) :: acc

  | Split (x_l, y, z, ec_l) ->
    let case x ec =
      ec, Obc.(S_affect (var env x, exp_var env y))
    in
    Obc.S_switch (exp_var env z, List.map2 case x_l ec_l) :: acc

  | Buffer _ ->
    invalid_arg "equation: buffer"

  | Delay _ ->
    failwith "unimplemented: delay"

  | Block bl ->
    let acc, w = clock_type env acc eq.eq_base_clock in
    let i = Ident.make_internal "i" in
    add_local_for_current_block_int env i;
    Obc.S_loop
      (find_var env i,
       w,
       Clock_types.max_burst_stream_type eq.eq_base_clock,
       Obc.S_block (block env bl))
    :: acc

and block env block =
  push_new_block env block.b_id;
  let body = List.fold_left (equation env) [] block.b_body in
  let locals = locals_per_block env block.b_id in
  pop_block env;
  {
    Obc.b_locals = locals;
    Obc.b_body = reset_if_machines env locals @ List.rev body;
  }

let node nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  let env = initial_env nd in

  let step =
    {
      Obc.m_name = step_name;
      Obc.m_inputs = List.map (find_var env) nd.n_input;
      Obc.m_outputs = List.map (find_var env) nd.n_output;
      Obc.m_body = block env nd.n_body;
    }
  in

  let fields = get_fields env in

  let reset =
    {
      Obc.m_name = reset_name;
      Obc.m_inputs = [];
      Obc.m_outputs = [];
      Obc.m_body =
        {
          Obc.b_locals = [];
          Obc.b_body = reset_if_machines env fields;
        }
    }
  in

  {
    Obc.ma_name = longname_of_node_name nd.n_name;
    Obc.ma_ctx = nd.n_orig_info#ni_ctx;
    Obc.ma_fields = fields;
    Obc.ma_methods = [reset; step];
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
