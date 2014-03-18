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

open Obc

(*
  Things to document:

  * General structure of the code

  * Calling convention

  * Runtime system

  push(&buffer_state, buffer_capacity, amount, data)

  vs.

  pop(&buffer_state, buffer_capacity, amount, result)
*)


(* {2 Environments} *)

(******************************************************************************)
(* {2 AST walking} *)

let rec translate_ty_local ty =
  match ty with
  | Ty_scal tys -> C.Scal tys
  | Ty_arr (ty, size) -> C.Array (translate_ty_local ty, size)
  | Ty_mach mty -> C.Struct (Backend_utils.mem_name mty.mt_name)

let rec translate_const cst =
  match cst with
  | C_scal c ->
    C.Const c
  | C_array a ->
    C.Array_lit (List.map translate_const a)
  | C_sizeof ty ->
    C.Sizeof (translate_ty ty)

(* let translate_inst local (env, defs) inst = *)
(*   let env, defs, ty = *)
(*     match inst.i_kind with *)
(*     | Mach ln -> *)
(*       env, defs, C.Name (mem_name ln) *)
(*     | Pword pw -> *)
(*       let env, defs = translate_pword env defs inst.i_name pw in *)
(*       env, defs, C.Name pword_mem *)
(*     | Buffer (ty, capacity) -> *)
(*       let ty = translate_ty_local ty in *)
(*       let env = add_buffer env inst.i_name local capacity ty in *)
(*       env, defs, C.Name buffer_mem *)
(*   in *)
(*   (env, defs), *)
(*   { *)
(*     C.v_name = inst.i_name; *)
(*     C.v_type = ty; *)
(*     C.v_init = None; *)
(*   } *)

(* let translate_var_dec ?(translate_ty = translate_ty_local) vd = *)
(*   { *)
(*     C.v_name = vd.v_name; *)
(*     C.v_type = translate_ty vd.v_type; *)
(*     C.v_init = None; *)
(*   } *)

(* let rec translate_lvalue lv = *)
(*   match lv with *)
(*   | Var v -> *)
(*     C.Var v *)
(*   | Index (id, e) -> *)
(*     C.Index (id, translate_exp e) *)

(* and translate_exp e = *)
(*   match e with *)
(*   | Const c -> *)
(*     C.(ConstExp (Const c)) *)
(*   | Lvalue lv -> *)
(*     C.Lvalue (translate_lvalue lv) *)

(* let translate_op op = *)
(*   match op with *)
(*   | "(+)" | "(-)" | "(\*\)" | "(/)" *)
(*   | "(<)" | "(<=)" | "(>)" | "(>=)" -> *)
(*     Some (String.sub op 1 (String.length op - 2)) *)
(*   | "(+.)" | "(-.)" | "(\*.)" | "(/.)" -> *)
(*     Some (String.sub op 1 1) *)
(*   | "(=)" -> *)
(*     Some "==" *)
(*   | _ -> *)
(*     None *)

(* let is_op op = translate_op op <> None *)

(* let rec translate_stm env acc stm = *)
(*   match stm with *)
(*   | Skip -> *)
(*     acc *)

(*   | Call { c_kind = Builtin op; c_inputs = x_l; c_outputs = y_l; } -> *)
(*     ( *)
(*       let open C in *)
(*       match translate_op op with *)
(*       | Some op -> *)
(*         let y = Utils.assert1 y_l in *)
(*         Affect *)
(*           ( *)
(*             translate_lvalue y, *)
(*             Op (op, List.map translate_exp x_l) *)
(*           ) *)
(*         :: acc *)
(*       | None -> *)
(*         Exp *)
(*           ( *)
(*             Call *)
(*               ( *)
(*                 op, *)
(*                 List.map translate_exp x_l *)
(*                 @ List.map (fun lv -> AddrOf (translate_lvalue lv)) y_l *)
(*               ) *)
(*           ) *)
(*           :: acc *)
(*     ) *)

(*   | Call _ -> *)
(*     acc *)

(*   | Affect (lv, e) -> *)
(*     C.Affect (translate_lvalue lv, translate_exp e) :: acc *)

(*   | Box _ -> *)
(*     acc *)
(*   | Unbox _ -> *)
(*     acc *)

(*   | Push (b, amount, x) -> *)
(*     let open C in *)
(*     let lv, capacity, ty = find_buffer env b in *)
(*     Exp *)
(*       (Call *)
(*          ( *)
(*            push, *)
(*            [ *)
(*              AddrOf lv; *)
(*              C_utils.int capacity; *)
(*              Op ("*", [translate_exp amount; Sizeof ty]); *)
(*              Lvalue (Var x); *)
(*            ] *)
(*          ) *)
(*       ) *)
(*     :: *)
(*     acc *)

(*   | Pop (b, amount, x) -> *)
(*     let open C in *)
(*     let lv, capacity, ty = find_buffer env b in *)
(*     Exp *)
(*       (Call *)
(*          ( *)
(*            pop, *)
(*            [ *)
(*              AddrOf lv; *)
(*              C_utils.int capacity; *)
(*              Op ("*", [translate_exp amount; Sizeof ty]); *)
(*              AddrOf (Var x); *)
(*            ] *)
(*          ) *)
(*       ) *)
(*     :: *)
(*     acc *)

(*   | Reset _ -> *)
(*     acc *)

(*   | Switch _ -> *)
(*     acc *)

(*   | For _ -> *)
(*     acc *)

(*   | Block block -> *)
(*     C.Block (translate_block env block) :: acc *)

(* and translate_block env block = *)
(*   let locals = List.map translate_var_dec block.b_vars in *)
(*   let (env, local_pwords), locals = *)
(*     Utils.mapfold_left (translate_inst true) (env, locals) block.b_insts *)
(*   in *)
(*   let body = List.fold_left (translate_stm env) [] block.b_body in *)
(*   { *)
(*     C.b_locals = locals @ local_pwords; *)
(*     C.b_body = List.rev body; *)
(*   } *)

(* let translate_method env mach_name methd = *)
(*   let mem = Ident.make_internal "mem" in *)
(*   let env = set_mem env mem in *)
(*   let inputs = *)
(*     List.map *)
(*       (translate_var_dec ~translate_ty:translate_ty_input) *)
(*       methd.m_inputs *)
(*   in *)
(*   let outputs = *)
(*     List.map *)
(*       (translate_var_dec ~translate_ty:translate_ty_output) *)
(*       methd.m_outputs *)
(*   in *)
(*   { *)
(*     C.f_name = method_name mach_name methd.m_kind; *)
(*     C.f_output = None; *)
(*     C.f_input = *)
(*       { *)
(*         C.v_name = mem; *)
(*         C.v_type = C.Pointer (C.Struct (mem_name mach_name)); *)
(*         C.v_init = None; *)
(*       } *)
(*     :: inputs @ outputs; *)
(*     C.f_body = translate_block env methd.m_body; *)
(*   } *)

(* let translate_machine (source, header) mach = *)
(*   Ident.set_current_ctx mach.m_ctx; *)
(*   let env = initial_env mach in *)

(*   (\* Create internal memory with buffers, nodes and pword instantiations *\) *)
(*   let mem_name = mem_name mach.m_name in *)
(*   let (env, pword_vars), fields = *)
(*     Utils.mapfold_left (translate_inst false) (env, []) mach.m_insts *)
(*   in *)
(*   let mem = *)
(*     { *)
(*       C.s_name = mem_name; *)
(*       C.s_fields = fields; *)
(*     } *)
(*   in *)

(*   let fun_defs = List.map (translate_method env mach.m_name) mach.m_methods in *)
(*   let fun_decls = List.map fun_decl_of_fun_def fun_defs in *)

(*   let source = *)
(*     List.rev_map (fun d -> C.(Def (Df_function d))) fun_defs *)
(*     @ [C.Def (C.Df_struct mem)] *)
(*     @ List.map (fun d -> C.(Def (Df_static d))) pword_vars *)
(*     @ source *)
(*   in *)
(*   let header = *)
(*     List.rev_map (fun d -> C.(Decl (Dc_function d))) fun_decls *)
(*     @ [C.Decl (C.Dc_struct mem_name)] *)
(*     @ header *)
(*   in *)
(*   source, header *)

(* let translate_type_def td = *)
(*   C.Def *)
(*     ( *)
(*       C.Df_enum *)
(*         { *)
(*           C.e_name = td.Ast_misc.ty_name; *)
(*           C.e_tags = td.Ast_misc.ty_body; *)
(*         } *)
(*     ) *)

let translate file =
  (* let source, header = *)
  (*   List.fold_left translate_machine ([], []) file.f_machines *)
  (* in *)
  let header =
    (* let enums = List.map translate_type_def file.f_type_defs in *)
    {
      C.f_name = file.f_name;
      C.f_kind = C.Header;
      C.f_includes = ["nir"];
      C.f_body = [];
        (* enums @ List.rev header; *)
    }
  in
  let source =
    {
      C.f_name = file.f_name;
      C.f_kind = C.Source;
      C.f_includes = ["nir"; String.lowercase file.f_name];
      C.f_body = [];
      (* C.f_body = List.rev source; *)
    }
  in
  [header; source]

(* {2 Generated code} *)

let serialize_file file =
  let fn =
    let ext =
      match file.C.f_kind with
      | C.Source -> ".c"
      | C.Header -> ".h"
    in
    Filename.concat
      (Initial.get_current_file_directory ())
      (String.lowercase file.C.f_name ^ ext)
  in
  let oc = open_out fn in
  let fmt = Format.formatter_of_out_channel oc in
  C_printer.print_file fmt file;
  Format.fprintf fmt "@?";
  close_out oc

let code_for_file file =
  object
    val files = translate file
    method print fmt =
      List.iter (C_printer.print_file fmt) files
    method serialize () =
      List.iter serialize_file files
  end

(* {2 Putting it all together} *)

let file ctx file =
  ctx, code_for_file file

let pass =
  let open Pass_manager in
  P_transform
    (make_transform
       ~ext:"c.tmp"
       ~print_out:Target.print_target_code
       "target_c"
       file)
