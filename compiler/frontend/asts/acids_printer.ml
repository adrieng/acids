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

module Make = functor (A : Acids.A) ->
struct
  open A

  let print_info p fmt x =
    if Compiler_options.has_something_to_print ()
    then Format.fprintf fmt " (*%a *)" p x
    else ()

  let rec print_clock_exp fmt ce =
    Format.fprintf fmt "@[%a%a@]"
      print_clock_exp_desc ce.ce_desc
      (print_info I.print_clock_exp_info) ce.ce_info

  and print_static_word fmt pw =
    Ast_misc.print_upword print_static_exp print_static_exp fmt pw

  and print_clock_exp_desc fmt ced =
    match ced with
    | Ce_condvar v -> I.print_var fmt v
    | Ce_pword p -> print_static_word fmt p
    | Ce_equal (ce, se) ->
      Format.fprintf fmt "(%a = %a)" print_clock_exp ce print_static_exp se

  and print_static_exp fmt se =
    Format.fprintf fmt "@[%a%a@]"
      (I.print_static_exp_desc print_static_exp) se.se_desc
      (print_info I.print_static_exp_info) se.se_info

  and print_exp fmt e =
    Format.fprintf fmt "@[%a%a@]"
      print_exp_desc e.e_desc
      (print_info I.print_exp_info) e.e_info

  and print_exp_desc fmt ed =
    match ed with
    | E_var v -> I.print_var fmt v
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
    | E_split (ce, e, ec_l) ->
      Format.fprintf fmt "@[split %a@ with %a by %a@]"
        print_exp e
        print_clock_exp ce
        (Utils.print_list_r Ast_misc.print_econstr ",") ec_l
    | E_bmerge (ce, e1, e2) ->
      Format.fprintf fmt "@[merge %a@ %a@ %a@]"
        print_clock_exp ce
        print_exp e1
        print_exp e2
    | E_merge (ce, c_l) ->
      Format.fprintf fmt "@[@[<hv 2>merge %a with%a@]@ end@]"
        print_clock_exp ce
        (Utils.print_list print_clause) c_l
    | E_valof ce ->
      Format.fprintf fmt "<@[%a@]>" print_clock_exp ce
    | E_clock_annot (e, ck) ->
      Format.fprintf fmt "(%a :: %a)"
        print_exp e
        print_clock_annot ck
    | E_type_annot (e, ty) ->
      Format.fprintf fmt "(%a : %a)"
        print_exp e
        Data_types.print_ty ty
    | E_spec_annot (e, spec) ->
      Format.fprintf fmt "%a in %a"
        print_exp e
        print_spec spec
    | E_dom (e, dom) ->
      print_dom fmt dom e
    | E_buffer (e, bu) ->
      Format.fprintf fmt "@[(buffer@ %a%a)@]"
        print_exp e
        (print_info I.print_buffer_info) bu.bu_info

  and print_app fmt app =
    Format.fprintf fmt "@[%a%a@]"
      Names.print_longname app.a_op
      (print_info I.print_app_info) app.a_info

  and print_block fmt block =
    Format.fprintf fmt "@[<hv 2>rec %a%a@]"
      (Utils.print_list_l print_eq "and ") block.b_body
      (print_info I.print_block_info) block.b_info

  and print_eq fmt eq =
    match eq.eq_desc with
    | Eq_plain (lhs, rhs) ->
      Format.fprintf fmt "@[%a%a =@ %a@]"
        print_pat lhs
        (print_info I.print_eq_info) eq.eq_info
        print_exp rhs
    | Eq_condvar (v, specs, rhs) ->
      let print_spec fmt spec =
        Format.fprintf fmt " in %a"
          print_spec spec
      in
      Format.fprintf fmt "@[cond %a%a =@ %a@]"
        I.print_var v
        (Utils.print_list print_spec) specs
        print_exp rhs

  and print_pat fmt p =
    Format.fprintf fmt "@[%a%a@]"
      print_pat_desc p.p_desc
      (print_info I.print_pat_info) p.p_info

  and print_pat_desc fmt pd =
    match pd with
    | P_var v -> I.print_var fmt v
    | P_tuple p_l ->
      Format.fprintf fmt "(@[%a@])"
        (Utils.print_list_r print_pat ",") p_l
    | P_clock_annot (p, ck) ->
      Format.fprintf fmt "(%a :: %a)"
        print_pat p
        print_clock_annot ck
    | P_type_annot (p, ty) ->
      Format.fprintf fmt "(%a : %a)"
        print_pat p
        Data_types.print_ty ty
    | P_spec_annot (p, spec) ->
      Format.fprintf fmt "(%a in %a)"
        print_pat p
        print_spec spec
    | P_split p_t ->
      Ast_misc.print_upword print_pat print_static_exp fmt p_t

  and print_clause fmt clause =
    Format.fprintf fmt "@ | @[<hv 2>%a ->@ %a@]"
      Ast_misc.print_econstr clause.c_sel
      print_exp clause.c_body

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

  and print_spec fmt spec =
    match spec.s_desc with
    | Unspec -> Format.fprintf fmt "unspec"
    | Word w -> Tree_word.print_upword print_static_exp print_static_exp fmt w
    | Interval (l, u) ->
      Format.fprintf fmt "@[[%a,@ %a]@]"
        print_static_exp l
        print_static_exp u

  let print_node_def fmt nd =
    let print_pragmas fmt pragmas =
      match pragmas with
      | [] -> ()
      | _ :: _ ->
        Format.fprintf fmt "@[%a@]@\n"
          (Utils.print_list_r Pragma.print_pragma "") pragmas
    in
    Format.fprintf fmt "@[%a@[<hov 2>let %snode@ %a%a@ %a =@ %a@]@]"
      print_pragmas nd.n_pragma
      (if nd.n_static then "static " else "")
      Names.print_shortname nd.n_name
      (print_info I.print_node_info) nd.n_info
      print_pat nd.n_input
      print_exp nd.n_body

  let print_node_decl fmt decl =
    Format.fprintf fmt
      "@[val %a@ : %a@ :: %a@ is %a@]"
      Names.print_shortname decl.decl_name
      Data_types.print_sig decl.decl_data
      Clock_types.print_sig decl.decl_clock
      Static_types.print_sig decl.decl_static

  let print_type_def fmt tydef =
    Format.fprintf fmt "@[type %a =@ %a@]"
      Names.print_shortname tydef.ty_name
      (Utils.print_list_r Names.print_shortname "|") tydef.ty_body

  let print_static_def fmt sdef =
    Format.fprintf fmt "@[let static %a =@ %a@]"
      Names.print_shortname sdef.sd_name
      print_exp sdef.sd_body

  let print_phrase fmt phr =
    (
      match phr with
      | Phr_node_def def -> print_node_def fmt def
      | Phr_node_decl decl -> print_node_decl fmt decl
      | Phr_type_def tydef -> print_type_def fmt tydef
      | Phr_static_def sdef -> print_static_def fmt sdef
    );
    Format.fprintf fmt "@\n"

  let print_file fmt file =
    let print_import fmt modn =
      Format.fprintf fmt "open %a@\n" Names.print_modname modn
    in
    Utils.print_list_eol print_import fmt file.f_imports;
    if List.length file.f_imports > 0 then Format.fprintf fmt "@\n";
    Utils.print_list_eol print_phrase fmt file.f_body
end
