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

module Make(A : Nir.A) =
struct
  open A

  let print_block_id fmt (Block_id id) = Format.fprintf fmt "'blk%d" id

  let print_clock_id fmt (Clock_id id) = Format.fprintf fmt "'a%d" id

  let print_buffer_polarity fmt pol =
    match pol with
    | Strict -> Format.fprintf fmt "strict"
    | Lazy -> Format.fprintf fmt "lazy"

  let rec print_ty fmt ty =
    match ty with
    | Ty_var i ->
      Data_types.(print_ty fmt (Ty_var i))
    | Ty_scal tys ->
      Data_types.print_ty_scal fmt tys
    | Ty_boxed ->
      Format.fprintf fmt "boxed"
    | Ty_clock ->
      Format.fprintf fmt "clock"
    | Ty_buffer (tys, size, pol) ->
      Format.fprintf fmt "buffer (%a, %a, %a)"
        print_ty tys
        Int.print size
        print_buffer_polarity pol

  let print_clock_var fmt cv =
    match cv with
    | Cv_clock v -> print_clock_id fmt v
    | Cv_block v -> print_block_id fmt v

  let print_clock fmt ck =
    Clock_types.print_raw_stream_type print_clock_var fmt ck

  let print_with_info print fmt ty ck x =
    Format.fprintf fmt "(@[";
    print fmt x;
    if !Compiler_options.print_all_info || !Compiler_options.print_data_info
    then Format.fprintf fmt "@ @[:type %a@]" print_ty ty;
    if !Compiler_options.print_all_info || !Compiler_options.print_clock_info
    then Format.fprintf fmt "@ @[:clock %a@]" print_clock ck;
    Format.fprintf fmt "@])"

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
      Ast_misc.print_const_pword fmt pw
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
      "(@[:delay %b@ :size %a :real_size %a@])"
      b.b_delay
      Int.print b.b_size
      Int.print b.b_real_size

  let print_buffer_direction fmt dir =
    match dir with
    | Push -> Format.fprintf fmt "push"
    | Pop -> Format.fprintf fmt "pop"

  let print_op fmt op =
    match op with
    | Node nn -> I.print_node_name fmt nn
    | Box -> Format.fprintf fmt "box"
    | Unbox -> Format.fprintf fmt "unbox"
    | Index -> Format.fprintf fmt "index"
    | BufferAccess (dir, pol) ->
      Format.fprintf fmt "%a_%a"
        print_buffer_direction dir
        print_buffer_polarity pol

  let print_app fmt app = print_op fmt app.a_op

  let rec print_eq_desc print_var fmt p =
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

    | Delay (x, y) ->
      Format.fprintf fmt "%a = (@[delay %a@])"
        print_var x
        print_var y

    | Block block ->
      print_block print_var fmt block

    | Pword (x, p) ->
      Format.fprintf fmt "%a = %a"
        print_var x
        Ast_misc.print_const_pword p

  and print_eq print_var fmt eq =
    Format.fprintf fmt "@[(@[<v 2>";
    print_eq_desc print_var fmt eq.eq_desc;
    if !Compiler_options.print_all_info || !Compiler_options.print_clock_info
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

  let print_var_dec fmt vd =
    let print_plain fmt vd =
      Format.fprintf fmt "%a@ :scope %a@ :annots %a"
        Ident.print vd.v_name
        print_scope vd.v_scope
        (print_list print_annot) vd.v_annots
    in
    print_with_info print_plain fmt vd.v_data vd.v_clock vd

  let print_node fmt node =
    let print_env fmt env =
      let r = ref (Ident.Env.cardinal env) in
      let print_binding k v =
        Format.fprintf fmt "(%a %a)"
          Ident.print k
          print_var_dec v;
        decr r;
        if !r > 0 then Format.fprintf fmt "@ "
      in
      Format.fprintf fmt "(@[<v 0>";
      Ident.Env.iter print_binding env;
      Format.fprintf fmt "@])"
    in
    Format.fprintf fmt
      "@[(@[<v 2>node@ :name %a@ :input %a@ :output %a@ :env %a@ :block_count %d"
      I.print_node_name node.n_name
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

  let print_file fmt file =
    Format.fprintf fmt
      "@[(@[<v 2>file@ :name %a@ :types %a@ :body %a@]@,)@]@\n"
      Names.print_shortname file.f_name
      (print_list print_type_def) file.f_type_defs
      (print_list print_node) file.f_body
end
