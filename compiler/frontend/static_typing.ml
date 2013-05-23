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

(** {1 Static typing} *)

(** Static typing is a very simple (two-element) type system used to distinguish
    which nodes have to be inlined. It drives static evaluation later on. *)

(** {2 Errors} *)

type error = unit

exception Typing_error of error

let print_error fmt err =
  match err with
  | () -> ()

(** {2 Unification} *)



(** {2 Moving from pretypes to types} *)

let type_file
    ctx
    (file
       : < interfaces : Interface.t Names.ShortEnv.t > Acids_interval.file) =
  ((assert false)
      :
      Pass_manager.ctx
   * < interfaces : Interface.t Names.ShortEnv.t > Acids_preclock.file)
  (* let intermediate_file = type_file file in *)
  (* let final_file = EXTRACT.extract_file intermediate_file in *)
  (* ctx, final_file *)

(** {2 Putting it all together} *)

let type_ =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_preclock.print_file
       "static_typing"
       type_file)
