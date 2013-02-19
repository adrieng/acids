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

type 'a var_dec =
    {
      v_ident : Ident.t;
      v_info : 'a;
      v_loc : Loc.t;
    }

type 'a clock_type =
  | Ct_var of Acids_misc.Ct_var.t
  | Ct_tuple of 'a clock_type list
  | Ct_stream_type of 'a stream_type

and 'a stream_type =
  | St_var of Acids_misc.St_var.t
  | St_on of 'a stream_type * 'a clock_exp

and 'a clock_exp =
    {
      ce_desc : 'a clock_exp_desc;
      ce_loc : Loc.t;
      ce_info : 'a;
    }

and 'a clock_exp_desc =
  | Ce_var of Ident.t
  | Ce_pword of 'a clock_exp_pword
  | Ce_equal of 'a clock_exp * 'a exp
  | Ce_iter of 'a clock_exp

and 'a clock_exp_pword =
    {
      ep_prefix : ('a exp, 'a exp) Acids_misc.tree;
      ep_period : ('a exp, 'a exp) Acids_misc.tree;
    }

and 'a clock_annot =
| Ca_var of Acids_misc.Ca_var.t
| Ca_on of 'a clock_annot * 'a clock_exp

and 'a exp =
    {
      e_desc : 'a exp_desc;
      e_loc : loc;
      e_info : 'a;
    }

and 'a e_desc =
  | E_var of Ident.t
  | E_tuple of 'a exp list

  | E_app of app * 'a exp list
  | E_where of 'a exp * 'a block

  | E_when of 'a exp * 'a clock_exp
  | E_split of 'a clock_exp * 'a exp list
  | E_merge of 'a clock_exp * 'a exp list

  | E_mergepat of 'a exp Acids_misc.tree
  | E_valof of 'a clock_exp

  | E_clockannot of 'a exp * 'a clock_annot

and app =
  {
    a_op : op;
  }

and op =
| O_node of Names.longname


and 'a block =
    {
      b_decls : 'a var_dec Ident.Env.t;
      b_body : 'a eq list;
    }

and 'a eq =
    {
      eq_rhs : 'a pat;
      eq_lhs : 'a exp;
    }

and 'a pat =
  | P_ident of Ident.t
  | P_tuple of 'a pat list
  | P_split of ('a pat, 'a exp) Acid_misc.tree

type 'a node =
  {
    n_name : Names.longname;
    n_inputs : 'a var_dec list;
    n_body : 'a exp;
    n_env : 'a node Names.Env.t;
    n_info : 'a;
  }

type 'a file =
  {
    f_name : Names.modname;
    f_imports : Names.modname list;
    f_initial_env : 'a node Names.Env.t;
    f_nodes : 'a node list;
  }
