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
open Ast_misc
open Data_types

type pword_generator =
  scope -> Pword.pword -> Ident.t -> Nir.clock ->
  Nir_utils.ctx -> Nir_utils.ctx

(** {2 Utilities} *)

(*
  [| u(v) |] = l = |u|
               a = after(l)
               p = merge a [| u |] [| v |]
*)
let pword_generator_from_word_generator gen _ p p_x p_ck ctx =
  let old_eqs = ctx.Nir_utils.c_eqs in

  let new_block_id, ctx = Nir_utils.get_fresh_block_id ctx in
  let b_ck = Clock_types.St_var (Cv_block new_block_id) in
  let b_scope = Scope_internal new_block_id in
  let u_x = Ident.make_internal "u" in
  let v_x = Ident.make_internal "v" in

  let l = Ident.make_internal "l" in
  let l_vd =
    Nir_utils.make_var
      l
      (Ty_scal Data_types.Tys_int)
      b_ck
      (Scope_internal new_block_id)
      []
  in
  let l_eq =
    Nir_utils.make_eq
      (Const (l, Ast_misc.Cconstr (Ec_int (Pword.(size p.u)))))
      b_ck
  in

  let a = Ident.make_internal "a" in
  let a_vd =
    Nir_utils.make_var
      a
      (Ty_scal Tys_bool)
      b_ck
      (Scope_internal new_block_id)
      []
  in
  let a_eq =
    let op =
      Node (Names.(make_longname (Module "Pervasives") "after"), Clock_id 0)
    in
    Nir_utils.make_call
      op
      []
      b_ck
      [a]
      [l]
  in

  let a_ce =
    Nir_utils.make_clock_exp
      (Ce_condvar a)
      Data_types.Tys_bool
      b_ck
  in

  let p_x_eq =
    Nir_utils.make_eq
      (Merge (p_x, a_ce, [Ec_bool false, u_x; Ec_bool true, v_x]))
      b_ck
  in

  let ck_ce_a =
    Clock_types.Ce_condvar
      {
        Clock_types.cecv_name = a;
        Clock_types.cecv_bounds = Interval.bool;
        Clock_types.cecv_specs = [Ast_misc.Interval Interval.bool];
      }
  in
  let ck_u =
    Clock_types.St_on (b_ck, ck_ce_a)
  in
  let ck_v =
    Clock_types.St_on (b_ck, Clock_types.Ce_equal (ck_ce_a, Ec_bool false))
  in

  let ctx = gen b_scope p.Pword.u u_x ck_u ctx in
  let ctx = gen b_scope p.Pword.v v_x ck_v ctx in

  let p_block =
    Nir_utils.make_block
      new_block_id
      (l_eq :: a_eq :: p_x_eq :: ctx.Nir_utils.c_eqs)
      p_ck
  in

  let ctx =
    List.fold_left
      Nir_utils.add_var
      ctx
      [l_vd; a_vd]
  in
  Nir_utils.add_eq { ctx with Nir_utils.c_eqs = old_eqs; } p_block

(** {2 Generators} *)

let plain_word_generator scope w w_x w_ck ctx =
  let l = Ident.make_internal "w_l" in
  let l_vd =
    Nir_utils.make_var
      l
      (Ty_scal Data_types.Tys_int)
      w_ck
      scope
      []
  in
  let l_eq =
    Nir_utils.make_eq
      (Const (l, Ast_misc.Cconstr (Ec_int (Pword.(size w)))))
      w_ck
  in

  let cpt = Ident.make_internal "cpt" in
  let cpt_vd =
    Nir_utils.make_var
      cpt
      (Ty_scal Data_types.Tys_int)
      w_ck
      scope
      []
  in
  let cpt_eq =
    let op =
      Node (Names.(make_longname (Module "Pervasives") "periodic"), Clock_id 0)
    in
    Nir_utils.make_call
      op
      []
      w_ck
      [cpt]
      [l]
  in

  let gen_idx ctx i =
    let i_x = Ident.make_internal "i" in
    let i_vd =
      Nir_utils.make_var
        cpt
        (Ty_scal Data_types.Tys_int)
        w_ck
        scope
        []
    in
    let i_eq =
      Nir_utils.make_eq
        (Const (i_x, Ast_misc.Cconstr (Ast_misc.Ec_int i)))
        w_ck
    in
    Nir_utils.(add_eq (add_var ctx i_vd) i_eq), i_x
  in

  let w_t = Pword.to_tree_word w in
  let ctx, i_x_l =
    Utils.mapfold_left gen_idx ctx (Tree_word.flatten_word_int w_t)
  in

  let w_x_eq =
    Nir_utils.make_eq
      (Call
         ([w_x],
          {
            a_op = Index;
            a_stream_inst = [];
          },
          cpt :: i_x_l))
      w_ck
  in

  let w_vd =
    Nir_utils.make_var
      w_x
      (Ty_scal Data_types.Tys_int)
      w_ck
      scope
      []
  in

  let ctx =
    List.fold_left
      Nir_utils.add_var
      ctx
      [
        l_vd; cpt_vd; w_vd;
      ]
  in

  List.fold_left Nir_utils.add_eq ctx [l_eq; cpt_eq; w_x_eq]

let plain_generator scope p p_x p_ck ctx  =
  pword_generator_from_word_generator
    plain_word_generator
    scope
    p
    p_x
    p_ck
    ctx

(** {2 Putting it all together: generator table} *)

let (available_generators : (string * pword_generator) list)  =
  [
    "plain", plain_generator;
  ]
