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

module type S =
sig
  type var
  val print_var : Format.formatter -> var -> unit

  type clock_exp_info
  val print_clock_exp_info : Format.formatter -> clock_exp_info -> unit

  type exp_info
  val print_exp_info : Format.formatter -> exp_info -> unit

  type app_info
  val print_app_info : Format.formatter -> app_info -> unit

  type block_info
  val print_block_info : Format.formatter -> block_info -> unit

  type pat_info
  val print_pat_info : Format.formatter -> pat_info -> unit

  type eq_info
  val print_eq_info : Format.formatter -> eq_info -> unit

  type node_info
  val print_node_info : Format.formatter -> node_info -> unit
end

module Make = functor (S : S) ->
struct
  type clock_exp =
      {
        ce_desc : clock_exp_desc;
        ce_loc : Loc.t;
        ce_info : S.clock_exp_info;
      }

  and clock_exp_desc =
    | Ce_var of S.var
    | Ce_pword of (exp, exp) Ast_misc.upword
    | Ce_equal of clock_exp * exp
    | Ce_iter of clock_exp

  and clock_annot =
    | Ca_var of int
    | Ca_on of clock_annot * clock_exp

  and exp =
      {
        e_desc : exp_desc;
        e_loc : Loc.t;
        e_info : S.exp_info;
      }

  and exp_desc =
    | E_var of S.var (** variables *)
    | E_const of Ast_misc.const (** constants *)

    | E_fst of exp (** left projection *)
    | E_snd of exp (** right projection *)
    | E_tuple of exp list (** tuple *)

    | E_fby of exp * exp (** dervied operator followed-by *)
    | E_ifthenelse of exp * exp * exp (** derived operator if then else *)

    | E_app of app * exp (** application *)
    | E_where of exp * block (** local declarations *)

    | E_when of exp * clock_exp (** sampling *)
    | E_split of clock_exp * exp (** splitting (n-ary sampling) *)
    | E_merge of clock_exp * exp list (** merging *)

    | E_valof of clock_exp (** evaluating clock exps *)

    | E_clockannot of exp * clock_annot (** annotations for clock inference *)

    | E_dom of exp * domain (** clock domain *)

  and app =
      {
        a_op : op;
        a_info : S.app_info;
        a_loc : Loc.t;
      }

  and op =
    | O_node of Names.longname

  and block =
      {
        b_body : eq list;
        b_loc : Loc.t;
        b_info : S.block_info;
      }

  and eq =
      {
        eq_lhs : pat;
        eq_rhs : exp;
        eq_loc : Loc.t;
        eq_info : S.eq_info;
      }

  and pat =
      {
        p_desc : pat_desc;
        p_loc : Loc.t;
        p_info : S.pat_info;
      }

  and pat_desc =
    | P_var of S.var
    | P_tuple of pat list
    | P_clock_annot of pat * clock_annot
    | P_split of (pat, exp) Ast_misc.upword

  and domain =
      {
        d_base_clock : clock_annot option;
        d_par : bool;
      }

  type node_def =
      {
        n_name : Names.shortname;
        n_input : pat;
        n_body : exp;
        n_pragma : Pragma.t option;
        n_static : bool;
        n_loc : Loc.t;
        n_info : S.node_info;
      }

  type node_decl =
      {
        decl_name : Names.shortname;
        decl_data : Data_types.data_sig;
        decl_static : Static_types.static_sig;
        decl_interv : Interval_types.interval_sig;
        decl_clock : Clock_types.clock_sig;
      }

  type phrase =
    | Phr_node_def of node_def

  type 'a file =
      {
        f_name : Names.modname;
        f_imports : Names.modname list;
        f_info : 'a;
        f_body : phrase list;
      }
end
