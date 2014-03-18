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

(** {2 Stand-alone type definitions} *)

type idents = Ident.t list

type buffer_polarity = Strict | Lazy

type block_id = Block_id of int

type scope =
| Scope_context
| Scope_input
| Scope_output
| Scope_internal of block_id

type ty =
| Ty_scal of Data_types.data_ty_scal
| Ty_boxed
| Ty_buffer of ty * Int.t * buffer_polarity

type buffer_info =
  {
    b_delay : bool;
    b_real_size : Int.t;
    b_size : Int.t;
  }

type buffer_direction = Push | Pop

(** {2 NIR itself} *)

module type S =
sig
  type node_name
  val print_node_name : Format.formatter -> node_name -> unit
  val original_name : node_name -> Names.longname

  type clock_var
  val print_clock_var : Format.formatter -> clock_var -> unit
end

module type A =
sig
  module I : S

  type clock = I.clock_var Clock_types.raw_stream_type

  (** {2 Equations} *)

  type op =
  | Node of I.node_name
  | Box
  | Unbox
  | BufferAccess of Ident.t * buffer_direction * buffer_polarity

  type call =
    {
      c_op : op;
      c_stream_inst : (int * Clock_types.stream_type) list;
    }

  type conv_var =
    {
      cv_external_clock : clock;
      cv_internal_clock : clock;
      cv_direction : buffer_direction;
    }

  type eq =
    private
      {
        eq_desc : eq_desc;
        eq_base_clock : clock;
        eq_loc : Loc.t;
      }

  and eq_desc =
  | Var of Ident.t * Ident.t
  | Const of Ident.t * Ast_misc.const
  | Pword of Ident.t * Ast_misc.const_pword
  | Call of Ident.t list * call * Ident.t list
  | Merge of Ident.t * Ident.t * (Ast_misc.econstr * Ident.t) list
  | Split of Ident.t list * Ident.t * Ident.t * Ast_misc.econstr list
  | Buffer of Ident.t * buffer_info * Ident.t
  | Delay of Ident.t * Ident.t
  | Block of block

  and block =
    private
      {
        b_id : block_id;
        b_body : eq list;
        b_conv : conv_var Ident.Env.t;
        b_loc : Loc.t;
      }

  (** {2 Nodes and files} *)

  type annot =
  | Ann_type of ty
  | Ann_clock of clock
  | Ann_spec of Ast_misc.spec

  type var_dec =
    private
      {
        v_name : Ident.t;
        v_data : ty;
        v_clock : clock;
        v_scope : scope;
        v_annots : annot list;
        v_loc : Loc.t;
      }

  type node =
    private
      {
        n_name : I.node_name;
        n_orig_info : Acids_causal.Info.node_info;
        n_input : Ident.t list;
        n_output : Ident.t list;
        n_env : var_dec Ident.Env.t;
        n_body : block;
        n_loc : Loc.t;
      }

  type 'a file =
    {
      f_name : Names.shortname;
      f_type_defs : Ast_misc.type_def list;
      f_body : node list;
      f_info : 'a;
    }

  (** {2 Creation/access function} *)

  val make_node :
    ?loc:Loc.t ->
    I.node_name ->
    Acids_causal.Info.node_info ->
    input:Ident.t list ->
    output:Ident.t list ->
    env:var_dec Ident.Env.t ->
    body : block ->
    node

  val make_block :
    ?loc:Loc.t ->
    ?conv:conv_var Ident.Env.t ->
    block_id ->
    eq list ->
    block

  val make_eq : ?loc:Loc.t -> eq_desc -> clock -> eq

  val make_var_dec :
    ?loc:Loc.t ->
    ?annots:annot list ->
    Ident.t ->
    ty ->
    clock ->
    scope ->
    var_dec
end

module Make(S : S) =
struct
  module I = S

  type clock = I.clock_var Clock_types.raw_stream_type

  (** {2 Equations} *)

  type op =
  | Node of I.node_name
  | Box
  | Unbox
  | BufferAccess of Ident.t * buffer_direction * buffer_polarity

  type call =
    {
      c_op : op;
      c_stream_inst : (int * Clock_types.stream_type) list;
    }

  type conv_var =
    {
      cv_external_clock : clock;
      cv_internal_clock : clock;
      cv_direction : buffer_direction;
      (* the direction is given from the point of view of the block's
         internals. More concretely, Nir.Push means that the push should be done
         inside and pop outside (the variable is defined by the buffer) and
         symmetrically for Nir.Pop. *)
    }

  type eq =
    {
      eq_desc : eq_desc;
      eq_base_clock : clock;
      eq_loc : Loc.t;
    }

  and eq_desc =
  | Var of Ident.t * Ident.t
  | Const of Ident.t * Ast_misc.const
  | Pword of Ident.t * Ast_misc.const_pword
  | Call of idents * call * idents
  | Merge of Ident.t * Ident.t * (Ast_misc.econstr * Ident.t) list
  | Split of idents * Ident.t * Ident.t * Ast_misc.econstr list
  | Buffer of Ident.t * buffer_info * Ident.t
  | Delay of Ident.t * Ident.t
  | Block of block

  and block =
    {
      b_id : block_id;
      b_body : eq list;
      b_conv : conv_var Ident.Env.t;
      b_loc : Loc.t;
    }

  (** {2 Nodes and files} *)

  type annot =
  | Ann_type of ty
  | Ann_clock of clock
  | Ann_spec of Ast_misc.spec

  type var_dec =
    {
      v_name : Ident.t;
      v_data : ty;
      v_clock : clock;
      v_scope : scope;
      v_annots : annot list;
      v_loc : Loc.t;
    }

  type node =
    {
      n_name : I.node_name;
      n_orig_info : Acids_causal.Info.node_info;
      n_input : idents;
      n_output : idents;
      n_env : var_dec Ident.Env.t;
      n_body : block;
      n_loc : Loc.t;
    }

  type 'a file =
    {
      f_name : Names.shortname;
      f_type_defs : Ast_misc.type_def list;
      f_body : node list;
      f_info : 'a;
    }

  (** {2 Creation/access function} *)

  let make_node
      ?(loc = Loc.dummy)
      name
      orig_info
      ~input
      ~output
      ~env
      ~body =
    {
      n_name = name;
      n_orig_info = orig_info;
      n_input = input;
      n_output = output;
      n_env = env;
      n_body = body;
      n_loc = loc;
    }

  let make_block ?(loc = Loc.dummy) ?(conv = Ident.Env.empty) id body =
    {
      b_id = id;
      b_body = body;
      b_conv = conv;
      b_loc = loc;
    }

  let make_eq ?(loc = Loc.dummy) body base_clock =
    {
      eq_desc = body;
      eq_base_clock = base_clock;
      eq_loc = loc;
    }

  let make_var_dec
      ?(loc = Loc.dummy)
      ?(annots = [])
      name
      data
      clock
      scope =
    {
      v_name = name;
      v_data = data;
      v_clock = clock;
      v_scope = scope;
      v_annots = annots;
      v_loc = loc;
    }
end
