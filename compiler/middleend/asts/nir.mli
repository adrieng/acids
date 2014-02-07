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

module type S =
sig
  type node_name
  val print_node_name : Format.formatter -> node_name -> unit
end

module type A =
sig
  module I : S

  (** {2 Type definitions} *)

  type idents = Ident.t list

  type block_id = Block_id of int

  type clock_id = Clock_id of int

  type buffer_polarity = Strict | Lazy

  (** {3 Simple data types} *)

  type ty =
  | Ty_var of int
  | Ty_scal of Data_types.data_ty_scal
  | Ty_boxed
  | Ty_clock
  | Ty_buffer of ty * Int.t * buffer_polarity

  type clock_var = Cv_clock of clock_id | Cv_block of block_id

  type clock = clock_var Clock_types.raw_stream_type

  (** {3 Clock expressions} *)

  type clock_exp =
    {
      ce_desc : clock_exp_desc;
      ce_bounds : Interval.t;
      ce_data : Data_types.data_ty_scal;
      ce_clock : clock;
      ce_loc : Loc.t;
    }

  and clock_exp_desc =
  | Ce_condvar of Ident.t
  | Ce_pword of Ast_misc.const_pword
  | Ce_equal of clock_exp * Ast_misc.econstr

  (** {2 Equations} *)

  type buffer_info =
    {
      b_delay : bool;
      b_real_size : Int.t;
      b_size : Int.t;
    }

  type buffer_direction = Push | Pop

  type op =
  | Node of I.node_name
  | Box
  | Unbox
  | Index
  | BufferAccess of buffer_direction * buffer_polarity

  type call =
    {
      a_op : op;
      a_stream_inst : (int * Clock_types.stream_type) list;
    }

  type merge_clause =
    {
      c_sel : Ast_misc.econstr;
      c_body : Ident.t;
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
  | Call of idents * call * idents
  | Merge of Ident.t * clock_exp * (Ast_misc.econstr * Ident.t) list
  | Split of idents * clock_exp * Ident.t * Ast_misc.econstr list
  | Valof of Ident.t * clock_exp
  | Buffer of Ident.t * buffer_info * Ident.t
  | Delay of Ident.t * Ident.t
  | Block of block

  and block =
    private
      {
        b_id : block_id;
        b_body : eq list;
        b_loc : Loc.t;
      }

  (** {2 Nodes and files} *)

  type scope =
  | Scope_context
  | Scope_internal of block_id

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
        n_input : idents;
        n_output : idents;
        n_env : var_dec Ident.Env.t;
        n_block_count : int;
        n_body : block;
        n_loc : Loc.t;
      }

  type type_def =
    {
      ty_name : Names.shortname;
      ty_body : Names.shortname list;
      ty_loc : Loc.t;
    }

  type 'a file =
    {
      f_name : Names.shortname;
      f_type_defs : type_def list;
      f_body : node list;
      f_info : 'a;
    }

  (** {2 Creation/access function} *)

  val make_node :
    ?loc:Loc.t ->
    I.node_name ->
    Acids_causal.Info.node_info ->
    input:idents ->
    output:idents ->
    env:var_dec Ident.Env.t ->
    block_count:int ->
    body : block ->
    node

  val make_block : ?loc:Loc.t -> block_id -> eq list -> block

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

module Make : functor (S : S) -> A with module I = S
