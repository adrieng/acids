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

open Acids_prespec

(** {2 Errors} *)

type error =
  | Non_cond_declared_var of Loc.t * Ident.t
  | Non_interval_annotated_var of Loc.t * Ident.t

exception Annotation_error of error

let print_error fmt err =
  match err with
  | Non_cond_declared_var (l, id) ->
    Format.fprintf fmt
      "%aVariable %a must be of type cond but has not been declared so"
      Loc.print l
      Ident.print id
  | Non_interval_annotated_var (l, id) ->
    Format.fprintf fmt
      "%aVariable %a has not been annotated with an interval"
      Loc.print l
      Ident.print id

let non_cond_declared_var l id =
  raise (Annotation_error (Non_cond_declared_var (l, id)))

let non_interval_annotated_var l id =
  raise (Annotation_error (Non_interval_annotated_var (l, id)))

(** {2 Environment} *)

type env =
  {
    intf_env : Interface.env;
    env : Ast_misc.spec list Ident.Env.t;
  }

let initial_env intf_env =
  {
    intf_env = intf_env;
    env = Ident.Env.empty;
  }

let add_spec id specs env =
  { env with env = Ident.Env.add id specs env.env; }

(** {2 AST walking} *)

let trad_spec spec =
  match spec.s_desc with
  | Unspec -> Ast_misc.Unspec
  | Interval (l, u) ->
    let l = Ast_misc.get_int l.se_desc in
    let u = Ast_misc.get_int u.se_desc in
    Ast_misc.Interval (Interval.make l u)
  | Word p ->
    let get_int se = Ast_misc.get_int se.se_desc in
    Ast_misc.Word (Tree_word.map_upword get_int get_int p)

let rec enrich_env_with_pattern env p =
  match p.p_desc with
  | P_var id ->
    let rec check_no_cond loc id ty =
      let open Data_types in
      match ty with
      | Ty_scal _ | Ty_var _ -> ()
      | Ty_cond _ -> non_cond_declared_var loc id
      | Ty_prod ty_l -> List.iter (check_no_cond loc id) ty_l
    in
    check_no_cond p.p_loc id p.p_info#pi_data; env
  | P_condvar (id, specs) ->
    let specs = List.map trad_spec specs in
    let specs =
      let open Data_types in
      match p.p_info#pi_data with
      | Ty_scal Tys_bool -> Ast_misc.Interval Interval.bool :: specs
      | _ -> specs
    in
    add_spec id specs env
  | P_tuple p_l -> List.fold_left enrich_env_with_pattern env p_l
  | P_clock_annot (p, _) | P_type_annot (p, _) | P_spec_annot (p, _) ->
    enrich_env_with_pattern env p
  | P_split pw ->
    Tree_word.fold_upword
      (fun p env -> enrich_env_with_pattern env p)
      (fun _ env -> env)
      pw
      env

(** {2 Putting it all together} *)

let annot_file
    ctx
    (file :
     <
       interfaces : Interface.env;
       static_nodes : Acids_static.node_def list
     > Acids_prespec.file) =
  (
    assert false
      :
      Pass_manager.ctx *
    <
      interfaces : Interface.env;
      static_nodes : Acids_static.node_def list
    > Acids_spec.file
  )

let annot :
    (< interfaces : Interface.env;
       static_nodes : Acids_static.node_def list > Acids_prespec.file ->
     < interfaces : Interface.env;
       static_nodes : Acids_static.node_def list; > Acids_spec.file)
 Pass_manager.pass
    =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_spec.print_file
       "spec_annot"
       annot_file)
