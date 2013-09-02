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

  type const_exp_info
  val print_const_exp_info : Format.formatter -> const_exp_info -> unit

  type 'a const_exp_desc
  val print_const_exp_desc :
    (Format.formatter -> 'a -> unit) ->
    Format.formatter ->
    'a const_exp_desc ->
    unit
  val map_const_exp_desc :
    ('a -> 'b) ->
    'a const_exp_desc ->
    'b const_exp_desc

  type exp_info
  val print_exp_info : Format.formatter -> exp_info -> unit

  type app_info
  val print_app_info : Format.formatter -> app_info -> unit

  type buffer_info
  val print_buffer_info : Format.formatter -> buffer_info -> unit

  type block_info
  val print_block_info : Format.formatter -> block_info -> unit

  type pat_info
  val print_pat_info : Format.formatter -> pat_info -> unit

  type eq_info
  val print_eq_info : Format.formatter -> eq_info -> unit

  type domain_info
  val print_domain_info : Format.formatter -> domain_info -> unit

  type node_info
  val print_node_info : Format.formatter -> node_info -> unit
end

module type A =
sig
  module I : S

  type clock_exp = {
    ce_desc : clock_exp_desc;
    ce_loc : Loc.t;
    ce_info : I.clock_exp_info;
  }

  and clock_exp_desc =
  | Ce_condvar of I.var
  | Ce_pword of pword_desc
  | Ce_equal of clock_exp * const_exp

  and pword_desc =
  | Pd_lit of const_word
  | Pd_global of Names.longname

  and const_word = (const_exp, const_exp) Tree_word.t

  and const_exp =
    {
      se_desc : const_exp I.const_exp_desc;
      se_loc : Loc.t;
      se_info : I.const_exp_info;
    }

  and clock_annot = Ca_var of int | Ca_on of clock_annot * clock_exp

  and exp = { e_desc : exp_desc; e_loc : Loc.t; e_info : I.exp_info; }

  and exp_desc =
  | E_var of I.var
  | E_const of Ast_misc.const
  | E_fst of exp
  | E_snd of exp
  | E_tuple of exp list
  | E_fby of exp * exp
  | E_ifthenelse of exp * exp * exp
  | E_app of app * exp
  | E_where of exp * block
  | E_when of exp * clock_exp
  | E_split of clock_exp * exp * Ast_misc.econstr list
  | E_bmerge of clock_exp * exp * exp
  | E_merge of clock_exp * merge_clause list
  | E_valof of clock_exp
  | E_clock_annot of exp * clock_annot
  | E_type_annot of exp * Data_types.data_ty
  | E_spec_annot of exp * spec
  | E_dom of exp * domain
  | E_buffer of exp * buffer

  and app = {
    a_op : Names.longname;
    a_loc : Loc.t;
    a_info : I.app_info;
  }

  and block = { b_body : eq list; b_loc : Loc.t; b_info : I.block_info; }

  and eq =
    {
      eq_desc : eq_desc;
      eq_loc : Loc.t;
      eq_info : I.eq_info;
    }

  and eq_desc =
  | Eq_plain of pat * exp
  | Eq_condvar of I.var * spec list * exp

  and pat = { p_desc : pat_desc; p_loc : Loc.t; p_info : I.pat_info; }

  and pat_desc =
  | P_var of I.var
  | P_tuple of pat list
  | P_clock_annot of pat * clock_annot
  | P_type_annot of pat * Data_types.data_ty
  | P_spec_annot of pat * spec
  | P_split of (pat, const_exp) Tree_word.t

  and merge_clause = {
    c_sel : Ast_misc.econstr;
    c_body : exp;
    c_loc : Loc.t;
  }

  and domain = {
    d_base_clock : clock_annot option;
    d_par : bool;
    d_info : I.domain_info;
  }

  and spec =
    {
      s_desc : spec_desc;
      s_loc : Loc.t;
    }

  and spec_desc =
  | Unspec
  | Word of (const_exp, const_exp) Tree_word.t
  | Interval of const_exp * const_exp

  and buffer =
    {
      bu_info : I.buffer_info;
    }

  type node_def = {
    n_name : Names.shortname;
    n_input : pat;
    n_body : exp;
    n_pragma : Pragma.t;
    n_const : bool;
    n_loc : Loc.t;
    n_info : I.node_info;
  }

  type node_decl = {
    decl_name : Names.shortname;
    decl_data : Data_types.data_sig;
    decl_const : Const_types.ty_sig;
    decl_clock : Clock_types.clock_sig;
    decl_loc : Loc.t;
  }

  type type_def = {
    ty_name : Names.shortname;
    ty_body : Names.shortname list;
    ty_loc : Loc.t;
  }

  type const_def =
    {
      sd_name : Names.shortname;
      sd_body : exp;
      sd_loc : Loc.t;
    }

  type pword_def =
    {
      pd_name : Names.shortname;
      pd_body : const_word;
      pd_loc : Loc.t;
    }

  type phrase =
  | Phr_node_def of node_def
  | Phr_node_decl of node_decl
  | Phr_type_def of type_def
  | Phr_const_def of const_def
  | Phr_pword_def of pword_def

  type 'a file = {
    f_name : Names.modname;
    f_imports : Names.modname list;
    f_info : 'a;
    f_body : phrase list;
  }
end

module Make = functor (S : S) ->
((
  struct
    module I = S

    type clock_exp =
      {
        ce_desc : clock_exp_desc;
        ce_loc : Loc.t;
        ce_info : S.clock_exp_info;
      }

    and clock_exp_desc =
    | Ce_condvar of I.var
    | Ce_pword of pword_desc
    | Ce_equal of clock_exp * const_exp

    and pword_desc =
    | Pd_lit of const_word
    | Pd_global of Names.longname

    and const_word = (const_exp, const_exp) Tree_word.t

    and const_exp =
      {
        se_desc : const_exp I.const_exp_desc;
        se_loc : Loc.t;
        se_info : I.const_exp_info;
      }

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

    | E_when of exp * clock_exp (** binary sampling *)
    | E_split of clock_exp * exp * Ast_misc.econstr list (** n-ary sampling *)

    | E_bmerge of clock_exp * exp * exp (** binary merge (1, 0) *)
    | E_merge of clock_exp * merge_clause list (** n-ary merge *)

    | E_valof of clock_exp (** evaluating clock exps *)

    | E_clock_annot of exp * clock_annot (** annotations for clock inference *)
    | E_type_annot of exp * Data_types.data_ty
    | E_spec_annot of exp * spec
    (** annotations for type inference *)

    | E_dom of exp * domain (** clock domain *)
    | E_buffer of exp * buffer

    and app =
      {
        a_op : Names.longname;
        a_loc : Loc.t;
        a_info : S.app_info;
      }

    and block =
      {
        b_body : eq list;
        b_loc : Loc.t;
        b_info : S.block_info;
      }

    and eq =
      {
        eq_desc : eq_desc;
        eq_loc : Loc.t;
        eq_info : S.eq_info;
      }

    and eq_desc =
    | Eq_plain of pat * exp
    | Eq_condvar of S.var * spec list * exp

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
    | P_type_annot of pat * Data_types.data_ty
    | P_spec_annot of pat * spec
    | P_split of (pat, const_exp) Tree_word.t

    and merge_clause =
      {
        c_sel : Ast_misc.econstr;
        c_body : exp;
        c_loc : Loc.t;
      }

    and domain =
      {
        d_base_clock : clock_annot option;
        d_par : bool;
        d_info : S.domain_info;
      }

    and spec =
      {
        s_desc : spec_desc;
        s_loc : Loc.t;
      }

    and spec_desc =
    | Unspec
    | Word of (const_exp, const_exp) Tree_word.t
    | Interval of const_exp * const_exp

    and buffer =
      {
        bu_info : I.buffer_info;
      }

    type node_def =
      {
        n_name : Names.shortname;
        n_input : pat;
        n_body : exp;
        n_pragma : Pragma.t;
        n_const : bool;
        n_loc : Loc.t;
        n_info : S.node_info;
      }

    type node_decl =
      {
        decl_name : Names.shortname;
        decl_data : Data_types.data_sig;
        decl_const : Const_types.ty_sig;
        decl_clock : Clock_types.clock_sig;
        decl_loc : Loc.t;
      }

    type type_def =
      {
        ty_name : Names.shortname;
        ty_body : Names.shortname list;
        ty_loc : Loc.t;
      }

    type const_def =
      {
        sd_name : Names.shortname;
        sd_body : exp;
        sd_loc : Loc.t;
      }

    type pword_def =
      {
        pd_name : Names.shortname;
        pd_body : const_word;
        pd_loc : Loc.t;
      }

    type phrase =
    | Phr_node_def of node_def
    | Phr_node_decl of node_decl
    | Phr_type_def of type_def
    | Phr_const_def of const_def
    | Phr_pword_def of pword_def

    type 'a file =
      {
        f_name : Names.modname;
        f_imports : Names.modname list;
        f_info : 'a;
        f_body : phrase list;
      }
  end
 ) : A with module I = S)
