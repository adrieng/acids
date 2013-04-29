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

module Make = functor (S : Acids.S) ->
struct
  module Acids = Acids.Make(S)
  open Acids

  let print_full_info p fmt x =
    if !Compiler_options.print_full_info
    then Format.fprintf fmt " (* %a *)" p x
    else ()

  let rec print_clock_exp fmt ce =
    Format.fprintf fmt "%a%a"
      print_clock_exp_desc ce.ce_desc
      (print_full_info S.print_clock_exp_info) ce.ce_info

  and print_clock_exp_desc fmt ced =
    match ced with
    | Ce_var v -> S.print_var fmt v
    | Ce_pword { Ast_misc.u = u; Ast_misc.v = v; } ->
      Format.fprintf fmt "%a(%a)"
        (Ast_misc.print_power_tree print_exp print_exp) u
        (Ast_misc.print_power_tree print_exp print_exp) v
    | Ce_equal (ce, e) ->
      Format.fprintf fmt "%a = %a" print_clock_exp ce print_exp e
    | Ce_iter ce ->
      Format.fprintf fmt "iter %a" print_clock_exp ce

  and print_exp fmt e =
    Format.fprintf fmt "%a%a"
      print_exp_desc e.e_desc
      (print_full_info S.print_exp_info) e.e_info

  and print_exp_desc fmt ed =
    match ed with
    | E_var v -> S.print_var fmt v
    | E_const c -> Ast_misc.print_const fmt c
    | E_fst e -> Format.fprintf fmt "fst %a" print_exp e
    | E_snd e -> Format.fprintf fmt "snd %a" print_exp e
    | E_tuple e_l ->
      Format.fprintf fmt "(%a)"
        (Utils.print_list_r print_exp ",") e_l
    | E_fby (e1, e2) ->
      Format.fprintf fmt "%a@ fby %a" print_exp e1 print_exp e2
    | E_ifthenelse (e1, e2, e3) ->
      Format.fprintf fmt "@[if %a@ then %a@ else %a@]"
        print_exp e1
        print_exp e2
        print_exp e3
    | E_app (app, e) ->
      Format.fprintf fmt "%a %a"
        print_app app
        print_exp e
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
    | E_dom (e, dom) ->
      print_dom fmt dom e

  and print_app fmt app =
    let print_op fmt op =
      match op with
      | O_node ln -> Names.print_longname fmt ln
    in
    Format.fprintf fmt "%a%a"
      print_op app.a_op
      (print_full_info S.print_app_info) app.a_info

  and print_block fmt block =
    Format.fprintf fmt "@[rec %a%a@]"
      (Utils.print_list_r print_eq "and") block.b_body
      (print_full_info S.print_block_info) block.b_info

  and print_eq fmt eq =
    Format.fprintf fmt "@[%a = %a%a@]"
      print_pat eq.eq_lhs
      print_exp eq.eq_rhs
      (print_full_info S.print_eq_info) eq.eq_info

  and print_pat fmt p =
    Format.fprintf fmt "%a%a"
      print_pat_desc p.p_desc
      (print_full_info S.print_pat_info) p.p_info

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
      Ast_misc.print_upword print_pat print_exp fmt p_t

  and print_clock_annot fmt ck =
    match ck with
    | Ca_var i -> Format.fprintf fmt "'a%d" i
    | Ca_on (ck, ce) ->
      Format.fprintf fmt "@[%a on %a@]"
        print_clock_annot ck
        print_clock_exp ce

  and print_dom fmt dom e =
    let print_base_clock fmt ck =
      Format.fprintf fmt "@ base %a" print_clock_annot ck
    in
    Format.fprintf fmt "@[%sdom %a%a@]"
      (if dom.d_par then "par" else "")
      print_exp e
      (Utils.print_opt print_base_clock) dom.d_base_clock

  let print_node_def fmt nd =
    Format.fprintf fmt "@[let %snode@ %a@ %a =@ %a%a@]"
      (if nd.n_static then "static " else "")
      Names.print_shortname nd.n_name
      print_pat nd.n_input
      print_exp nd.n_body
      (print_full_info S.print_node_info) nd.n_info

  let print_node_decl fmt decl =
    Format.fprintf fmt
      "@[val %a@ : %a@ :: %a@ is %a@ in %a@]"
      Names.print_shortname decl.decl_name
      Data_types.print_sig decl.decl_data
      Static_types.print_sig decl.decl_static
      Interval_types.print_sig decl.decl_interv
      Clock_types.print_sig decl.decl_clock

  let print_phrase fmt phr =
    match phr with
    | Phr_node_def def -> print_node_def fmt def
    | Phr_node_decl decl -> print_node_decl fmt decl

  let print_file fmt file =
    let print_import fmt modn =
      Format.fprintf fmt "open %a@\n" Names.print_modname modn
    in
    Utils.print_list_eol print_import fmt file.f_imports;
    Utils.print_list_eol print_phrase fmt file.f_body;
    Format.fprintf fmt "@\n"
end
