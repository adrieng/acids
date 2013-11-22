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

(** {1 AST for the middle-end} *)

type block_id = Block_id of int

type clock_id = Clock_id of int

(** {2 Simple data types} *)

type ty =
  | Ty_var of int
  | Ty_scal of Data_types.data_ty_scal
  | Ty_boxed
  | Ty_clock

type clock_var =
  | Cv_clock of clock_id
  | Cv_block of block_id

type clock = clock_var Clock_types.raw_stream_type

(** {2 Clock expressions} *)

type 'a clock_exp =
  {
    ce_desc : 'a clock_exp_desc;
    ce_bounds : Interval.t;
    ce_data : Data_types.data_ty_scal;
    ce_clock : clock;
    ce_loc : Loc.t;
  }

and 'a clock_exp_desc =
  | Ce_condvar of 'a
  | Ce_pword of Ast_misc.const_pword
  | Ce_equal of 'a clock_exp * Ast_misc.econstr

(** {2 Equations} *)

type buffer_info =
  {
    b_delay : bool;
    b_real_size : Int.t; (* disrega*)
    b_size : Int.t;
  }

type op =
  | Node of Names.longname * clock_id
  (* node_name * base_clock_var_id, the latter being -1 if the call has not been
     sliced yet *)
  | Box
  | Unbox
  | Index (* static array indexing: first argument is index, rest is array *)

type call =
  {
    a_op : op;
    a_stream_inst : (int * Clock_types.stream_type) list;
  }

type 'a merge_clause =
  {
    c_sel : Ast_misc.econstr;
    c_body : 'a;
  }

type 'a eq =
  {
    eq_desc : 'a eq_desc;
    eq_base_clock : clock;
    eq_loc : Loc.t;
  }

and 'a eq_desc =
  | Var of 'a * 'a (** x = y *)
  | Const of 'a * Ast_misc.const (** x = c *)

  | Call of 'a list * call * 'a list
  (** x_1, ..., x_n = OP(y_1, ..., y_m) *)

  | Merge of 'a * 'a clock_exp * (Ast_misc.econstr * 'a) list
  (** x = merge ce (ec_1 -> y_1) ... (ec_n -> y_n) *)
  | Split of 'a list * 'a clock_exp * 'a * Ast_misc.econstr list
  (** x_1, ..., x_n = split y with ce by ec_1, ... ec_n *)

  | Valof of 'a * 'a clock_exp (** x = valof ce *)

  | Buffer of 'a * buffer_info * 'a (** x = buffer y *)
  | Delay of 'a * 'a (** x = delay y *)

  | Block of 'a block (** have to be scheduled together *)

and 'a block =
  {
    b_id : block_id;
    b_body : 'a eq list;
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

type 'i var_dec =
  {
    v_name : Ident.t;
    v_data : ty;
    v_clock : clock;
    v_scope : scope;
    v_annots : annot list;
    v_loc : Loc.t;
    v_info : 'i;
  }

type 'i node =
  {
    n_name : Names.shortname * clock_id;
    n_orig_info : Acids_causal.Info.node_info;

    n_input : Ident.t list;
    n_output : Ident.t list;

    n_env : 'i var_dec Ident.Env.t;
    n_block_count : int;
    n_body : Ident.t block;

    n_loc : Loc.t;
  }

type type_def =
  {
    ty_name : Names.shortname;
    ty_body : Names.shortname list;
    ty_loc : Loc.t;
  }

type ('var_info, 'file_info) file =
  {
    f_name : Names.shortname;
    f_type_defs : type_def list;
    f_body : 'var_info node list;
    f_info : 'file_info;
  }
