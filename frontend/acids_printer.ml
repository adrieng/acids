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

module Print = functor (S : Acids.S) ->
struct
  module Acids = Acids.Make(S)
  open Acids

  let rec print_clock_exp fmt ce =
    print_clock_exp_desc fmt ce.ce_desc

  and print_clock_exp_desc fmt ced =
    match ced with
    | Ce_var v -> S.print_var fmt v
    | Ce_pword
        {
          ep_prefix = ue;
          ep_period = ve;
        } ->
      Format.fprintf fmt "%a(%a)"
        (Ast_misc.print_power_tree print_exp print_exp) ue
        (Ast_misc.print_power_tree print_exp print_exp) ve
    | Ce_equal (ce, e) ->
      Format.fprintf fmt "%a = %a" print_clock_exp ce print_exp e
    | Ce_iter ce ->
      Format.fprintf fmt "iter %a" print_clock_exp ce

  and print_exp fmt e =
    print_exp_desc fmt e.e_desc

  and print_exp_desc fmt ed =
    match ed with
    | E_var v -> S.print_var fmt v
    | E_const c -> Ast_misc.print_const fmt c
    | E_fst e -> Format.fprintf fmt "fst %a" print_exp e
    | E_snd e -> Format.fprintf fmt "snd %a" print_exp e
    | E_tuple e_l ->
      Format.fprintf fmt "(%a)"
        (Utils.print_list_r print_exp ",") e_l
    | E_app (app, e_l) ->
      Format.fprintf fmt "%a(%a)"
        print_op app.a_op
        (Utils.print_list_r print_exp ",") e_l
    | E_where (e, bl) ->
      Format.fprintf fmt "@[%a where@ %a@]"
        print_exp e
        print_block bl
    | E_when (e, ce) ->
      Format.fprintf fmt "@[%a@ when %a@]"
        print_exp e
        print_clock_exp ce
    | E_split (ce, e) ->
      Format.fprintf fmt "@[split %a@ %a@]"
        print_clock_exp ce
        print_exp e
    | E_merge (ce, e_l) ->
      Format.fprintf fmt "@[merge@ %a (@[%a@])@]"
        print_clock_exp ce
        (Utils.print_list_r print_exp "") e_l
    | E_valof ce ->
      Format.fprintf fmt "?%a" print_clock_exp ce
    | E_clockannot (e, ck) ->
      Format.fprintf fmt "(%a :: %a)"
        print_exp e
        print_clock_annot ck
    | E_clockdom (e, dom) ->
      print_clock_dom fmt dom e

  and print_op fmt op =
    match op with
    | O_node ln -> Names.print_longname fmt ln

  and print_block fmt block =
    Format.fprintf fmt "@[rec %a@]"
      (Utils.print_list_r print_eq "and") block.b_body

  and print_eq fmt eq =
    Format.fprintf fmt "@[%a = %a@]"
      print_pat eq.eq_lhs
      print_exp eq.eq_rhs

  and print_pat fmt p =
    print_pat_desc fmt p.p_desc

  and print_pat_desc fmt pd =
    match pd with
    | P_var v -> S.print_var fmt v
    | P_tuple p_l ->
      Format.fprintf fmt "(@[%a@])"
        (Utils.print_list_r print_pat ",") p_l
    | P_clock_annot (p, ck) ->
      Format.fprintf fmt "(%a :: %a)"
        print_pat p
        print_clock_annot ck
    | P_split p_t ->
      Format.fprintf fmt "<%a>"
        (Ast_misc.print_power_tree print_pat print_exp) p_t

  and print_clock_annot fmt ck =
    match ck with
    | Ca_var i -> Format.fprintf fmt "'a%d" i
    | Ca_on (ck, ce) ->
      Format.fprintf fmt "@[%a on %a@]"
        print_clock_annot ck
        print_clock_exp ce

  and print_clock_dom fmt dom e =
    let print_base_clock fmt ck =
      Format.fprintf fmt "@ by %a" print_clock_annot ck
    in
    Format.fprintf fmt "@[%sdom %a%a@]"
      (if dom.d_par then "par" else "")
      print_exp e
      (Utils.print_opt print_base_clock) dom.d_base_clock
end
