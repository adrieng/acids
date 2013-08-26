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

open Nir

let print_ty fmt ty =
  match ty with
  | Ty_var i -> Data_types.(print_ty fmt (Ty_var i))
  | Ty_scal tys -> Data_types.print_ty_scal fmt tys
  | Ty_clock -> Format.fprintf fmt "clock"

let print_clock fmt ck =
  match ck with
  | Ck_var i ->
    Clock_types.(print_clock_type fmt (Ct_var i))
  | Ck_stream st ->
    Clock_types.print_stream_type fmt st
  | Ck_block_base ->
    Format.fprintf fmt "."

let print_with_info print fmt ty ck x =
  Format.fprintf fmt "(@[";
  print fmt x;
  if !Compiler_options.print_data_info
  then Format.fprintf fmt "@ @[:type %a@]@ " print_ty ty;
  if !Compiler_options.print_clock_info
  then Format.fprintf fmt "@ @[:clock %a@]@ " print_clock ck;
  Format.fprintf fmt "@])"

let print_block_id fmt (Block_id id) = Format.fprintf fmt "'blk%d" id

let print_clock_id fmt (Clock_id id) = Format.fprintf fmt "'a%d" id

let rec print_clock_exp print_var fmt ce =
  print_with_info
    (print_clock_exp_desc print_var)
    fmt
    (Ty_scal ce.ce_data)
    ce.ce_clock
    ce.ce_desc

and print_clock_exp_desc print_var fmt ced =
  match ced with
  | Ce_condvar v ->
    print_var fmt v
  | Ce_pword pw ->
    Ast_misc.print_static_pword fmt pw
  | Ce_equal (ce, ec) ->
    Format.fprintf fmt "(=)@ %a@ %a"
      (print_clock_exp print_var) ce
      Ast_misc.print_econstr ec

let print_merge_clause print_var fmt (sel, body) =
  Format.fprintf fmt "(@[%a@ %a@])"
    Ast_misc.print_econstr sel
    print_var body

let print_par p fmt x = Format.fprintf fmt "@[(%a@,)@]" p x

let print_list print fmt x_l =
  Format.fprintf fmt "%a"
    (print_par (Utils.print_list_r print "")) x_l

let print_buffer fmt b =
  Format.fprintf fmt
    "(@[:delay %b@ :size %a@])"
    b.b_delay
    Int.print b.b_size

let print_op fmt op =
  match op with
  | Builtin n -> Format.fprintf fmt "(builtin %a)" Names.print_shortname n
  | Node ln -> Names.print_longname fmt ln

let print_app fmt app = print_op fmt app.a_op

let rec print_process print_var fmt p =
  let print_var_tuple = print_list print_var in
  let print_clock_exp = print_clock_exp print_var in
  match p with
  | Var (x, y) ->
    Format.fprintf fmt "%a = %a"
      print_var x
      print_var y

  | Const (x, cst) ->
    Format.fprintf fmt "%a = %a"
      print_var x
      Ast_misc.print_const cst

  | Call (x_l, app, y_l) ->
    Format.fprintf fmt "%a = (@[%a@ %a@])"
      print_var_tuple x_l
      print_app app
      print_var_tuple y_l

  | Merge (x, ce, mc_l) ->
    Format.fprintf fmt "%a = (@[<v 2>merge %a@ %a@])"
      print_var x
      print_clock_exp ce
      (Utils.print_list_r (print_merge_clause print_var) "") mc_l

  | Split (x_l, ce, y, ec_l) ->
    Format.fprintf fmt "%a = (@[<v 2>split@ %a@ %a@ %a@])"
      print_var_tuple x_l
      print_clock_exp ce
      print_var y
      (print_list Ast_misc.print_econstr) ec_l

  | Valof (x, ce) ->
    Format.fprintf fmt "%a = (@[valof %a@])"
      print_var x
      print_clock_exp ce

  | Buffer (x, b, y) ->
    Format.fprintf fmt "%a = (@[<v 2>buffer@ %a@ %a@])"
      print_var x
      print_buffer b
      print_var y

  | Block block ->
    print_block print_var fmt block

and print_eq print_var fmt eq =
  Format.fprintf fmt "@[(@[<v 2>";
  print_process print_var fmt eq.eq_desc;
  if !Compiler_options.print_clock_info
  then
    Format.fprintf fmt "@ :base_clock %a" print_clock eq.eq_base_clock;
  Format.fprintf fmt "@]@,)@]"

and print_block print_var fmt block =
  Format.fprintf fmt
    "@[(@[<v 2>block@ :id %a@ :body (@[<v 0>%a@])@]@,)@]"
    print_block_id block.b_id
    (Utils.print_list_r (print_eq print_var) "") block.b_body

let print_scope fmt s =
  match s with
  | Scope_context -> Format.fprintf fmt "(context)"
  | Scope_internal id -> Format.fprintf fmt "(internal %a)" print_block_id id

let print_annot fmt ann =
  match ann with
  | Ann_type ty ->
    Format.fprintf fmt "(type %a)" print_ty ty
  | Ann_clock ck ->
    Format.fprintf fmt "(clock %a)" print_clock ck
  | Ann_spec spec ->
    Format.fprintf fmt "(spec %a)" Ast_misc.print_spec spec

let print_var_dec print_info fmt vd =
  let print_plain fmt vd =
    Format.fprintf fmt "%a@ :scope %a@ :annots %a"
      Ident.print vd.v_name
      print_scope vd.v_scope
      (print_list print_annot) vd.v_annots
    ;
    match print_info with
    | None -> ()
    | Some print_info -> Format.fprintf fmt "@ :info %a" print_info vd.v_info
  in
  print_with_info print_plain fmt vd.v_data vd.v_clock vd

let print_node print_info fmt node =
  let print_env fmt env =
    let r = ref (Ident.Env.cardinal env) in
    let print_binding k v =
      Format.fprintf fmt "(%a %a)"
        Ident.print k
        (print_var_dec print_info) v;
      decr r;
      if !r > 0 then Format.fprintf fmt "@ "
    in
    Format.fprintf fmt "(@[<v 0>";
    Ident.Env.iter print_binding env;
    Format.fprintf fmt "@])"
  in
  Format.fprintf fmt
    "@[(@[<v 2>node@ :name %a@ :input %a@ :output %a@ :env %a@ :block_count %d"
    Names.print_shortname node.n_name
    (print_list Ident.print) node.n_input
    (print_list Ident.print) node.n_output
    print_env node.n_env
    node.n_block_count
  ;
  Format.fprintf fmt "@ :body %a@]@,)@]"
    (print_block Ident.print) node.n_body

let print_type_def fmt td =
  Format.fprintf fmt
    "(@[<v 2>type@ :name %a@ :body %a@])"
    Names.print_shortname td.ty_name
    (print_list Names.print_shortname) td.ty_body

let print_file ?(print_info = None) fmt file =
  Format.fprintf fmt
    "@[(@[<v 2>file@ :name %a@ :types %a@ :body %a@]@,)@]@\n"
    Names.print_shortname file.f_name
    (print_list print_type_def) file.f_type_defs
    (print_list (print_node print_info)) file.f_body
