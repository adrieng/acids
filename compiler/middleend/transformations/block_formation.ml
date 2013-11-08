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

open Nir

(** {1 Block formation}

    This pass introduces blocks around some equations. The goal is to establish
    the following invariant: *polymorphic clock variables present in clock
    signatures are only instantiated with block base clocks*.

    For example, consider the node f with clock signature:

    f :: forall 'a. 'a on (1 0) -> 'a

    called with 'a instantiated to 'a on (3):

    y :: 'a on (3) = f (x :: 'a on (2 1)

    The block formation pass introduces a block such that the invariant is
    respected:

    block 1 :: 'a on (3)
      y :: 'blk1 = f (x :: 'blk1 on (1 0))
    end
*)

(** {2 Utility functions} *)

let mk_sampled_clock ce ec ck =
  Clock_types.(St_on (ck, Ce_equal (ce, ec)))

(** {2 Environments} *)

type env =
  {
    intf_env : Interface.env;
    local_clock_sigs : Clock_types.clock_sig Names.ShortEnv.t;
    mutable current_block_count : int;
    mutable var_decs : unit var_dec Ident.Env.t;
  }

let initial_env file =
  let local_clock_sigs =
    let add local_clock_sigs nd =
      Names.ShortEnv.add
        (fst nd.n_name)
        nd.n_orig_info#ni_clock local_clock_sigs
    in
    List.fold_left add Names.ShortEnv.empty file.f_body
  in
  {
    intf_env = file.f_info;
    local_clock_sigs = local_clock_sigs;
    current_block_count = 0;
    var_decs = Ident.Env.empty;
  }

let find_node_sig env ln =
  let open Names in
  match ln.modn with
  | LocalModule ->
    ShortEnv.find ln.shortn env.local_clock_sigs
  | Module modn ->
    let intf = ShortEnv.find modn env.intf_env in
    Interface.(clock_signature_of_node_item (find_node intf ln.shortn))

let enter_node env nd =
  env.var_decs <- nd.n_env;
  env.current_block_count <- nd.n_block_count

let get_current_block_count env = env.current_block_count

let fresh_block_id env =
  let next = env.current_block_count in
  env.current_block_count <- env.current_block_count + 1;
  Block_id next

let get_var_decs env = env.var_decs

let add_var_dec env vd =
  env.var_decs <- Ident.Env.add vd.v_name vd env.var_decs

let find_var_dec env id = Ident.Env.find id env.var_decs

(** {2 AST traversal} *)

let form_block
    env
    (* environment *)
    base_clock
    (* base_clock of the block to form *)
    mk_desc
    (* function creating the body of the expression *)
    x_l
    (* list of inputs *)
    x_mk_ck_l
    (* list of functions, one for each input, giving the corresponding input's
       clock from the new base clock *)
    y_l
    (* list of outputs *)
    y_mk_ck_l
    (* y_mk_ck_l is to y_l what x_mk_ck_l is to x_l *)
    =
  assert (List.length x_l = List.length x_mk_ck_l);
  assert (List.length y_l = List.length y_mk_ck_l);

  let bid = fresh_block_id env in
  let bck = Clock_types.St_var (Cv_block bid) in

  let refresh_variable eqs x mk_ck =
    let x_vd = find_var_dec env x in
    let x' = Ident.make_prefix "blk_" x in
    let x'_ck = mk_ck bck in
    let x'_vd = { x_vd with v_name = x'; v_clock = x'_ck; } in
    add_var_dec env x'_vd;
    Nir_utils.make_eq (Var (x', x)) bck :: eqs, x'
  in

  let eqs, x'_l = Utils.mapfold_left_2 refresh_variable [] x_l x_mk_ck_l in
  let eqs, y'_l = Utils.mapfold_left_2 refresh_variable eqs y_l y_mk_ck_l in
  let block =
    {
      b_id = bid;
      b_body = Nir_utils.make_eq (mk_desc x'_l y'_l) bck :: eqs;
      b_loc = Loc.dummy;
    }
  in
  Nir_utils.make_eq (Block block) base_clock

let rec equation env eq =
  match eq.eq_desc with
  | Var _ | Buffer _ | Call (_, { a_op = Box | Unbox; }, _) | Delay _ ->
    (* TODO: optimize buffer *)
    eq

  | Const (x, c) ->
    let mk_desc x_l _ =
      let x = Utils.assert1 x_l in
      Const (x, c)
    in
    form_block env eq.eq_base_clock mk_desc [x] [fun ck -> ck] [] []

  | Call (x_l, ({ a_op = Node (ln, Clock_id id); } as app), y_l) ->
    assert (id > Nir_utils.greatest_invalid_clock_id_int);
    let ty_sig = find_node_sig env ln in
    let inputs_st, outputs_st = Clock_types.slice_signature id ty_sig in
    let inputs_st =
      List.map Nir_utils.nir_stream_type_of_stream_type inputs_st
    in
    let outputs_st =
      List.map Nir_utils.nir_stream_type_of_stream_type outputs_st
    in
    let mk_desc x_l y_l =
      Call (x_l, app, y_l)
    in
    let x_l_mk_l = List.map Clock_types.reroot_stream_type inputs_st in
    let y_l_mk_l = List.map Clock_types.reroot_stream_type outputs_st in
    form_block
      env
      eq.eq_base_clock
      mk_desc
      x_l x_l_mk_l
      y_l y_l_mk_l

  | Merge (x, ce, c_l) ->
    let ec_l, y_l = List.split c_l in
    let mk_desc x_l y_l =
      let x = Utils.assert1 x_l in
      Merge (x, ce, List.combine ec_l y_l)
    in
    let ce = Nir_utils.clock_type_exp_of_nir_clock_exp ce in
    form_block
      env
      eq.eq_base_clock
      mk_desc
      [x] [fun ck -> ck]
      y_l (List.map (mk_sampled_clock ce) ec_l)

  | Split (x_l, ce, y, ec_l) ->
    let mk_desc x_l y_l =
      let y = Utils.assert1 y_l in
      Split (x_l, ce, y, ec_l)
    in
    let ce = Nir_utils.clock_type_exp_of_nir_clock_exp ce in
    form_block
      env
      eq.eq_base_clock
      mk_desc
      x_l (List.map (mk_sampled_clock ce) ec_l)
      [y] [fun ck -> ck]

  | Valof (x, ce) ->
    let y_l, y_l_mk_l =
      match Nir_utils.var_clock_exp ce with
      | None -> [], []
      | Some y -> [y], [fun ck -> ck]
    in
    let mk_desc x_l y_l =
      let x = Utils.assert1 x_l in
      Valof
        (x,
         match y_l with
          | [] -> ce
          | [y] -> Nir_utils.reroot_clock_exp ce y
          | _ :: _ :: _ -> assert false)
    in
    form_block
      env
      eq.eq_base_clock
      mk_desc
      [x] [fun ck -> ck]
      y_l y_l_mk_l

  | Block blk ->
    { eq with eq_desc = Block (block env blk); }

and block env block =
  assert (let Block_id x = block.b_id in x < get_current_block_count env);
  let body = List.map (equation env) block.b_body in
  { block with b_body = body; }

let node env nd =
  Ident.set_current_ctx nd.n_orig_info#ni_ctx;
  enter_node env nd;
  let block = block env nd.n_body in
  {
    nd with
      n_body = block;
      n_block_count = get_current_block_count env;
      n_env = get_var_decs env;
  }

let tr ctx file =
  let env = initial_env file in
  Middleend_utils.map_to_nodes (node env) ctx file

let pass =
  Middleend_utils.(make_transform "block_formation" tr)
