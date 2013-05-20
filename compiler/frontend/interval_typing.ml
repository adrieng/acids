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

open Acids_typed
open Interval_types

(** {1 Interval typing}

    Nothing special for now. *)

(** {2 Errors} *)

type error =
  | Non_exhaustive_pattern of Loc.t * Ast_misc.econstr

exception Typing_error of error

let print_error fmt err =
  match err with
  | Non_exhaustive_pattern (l, ec) ->
    Format.fprintf fmt "%aThis pattern-matching is not exhaustive@\n"
      Loc.print l;
    Format.fprintf fmt "Here is an example of a value that is not matched:@\n%a"
      Ast_misc.print_econstr ec

let non_exhaustive_pattern loc ec =
  raise (Typing_error (Non_exhaustive_pattern (loc, ec)))

(** {2 Constraints and unification} *)

(* {2 Typing environments} *)

type typing_env =
  {
    intf_env : Interface.t Names.ShortEnv.t;
    current_types : Names.shortname list Names.ShortEnv.t;
    current_nodes : interval_sig Names.ShortEnv.t;
    idents : unit Ident.Env.t;
  }

(** {2 Typing AST nodes} *)

let type_file
    ctx
    (file : < interfaces : Interface.t Names.ShortEnv.t > Acids_typed.file) =
  (assert false
     :
     Pass_manager.ctx
     * < interfaces : Interface.t Names.ShortEnv.t > Acids_interval.file)

(** {2 Putting it all together} *)

let type_ =
  let open Pass_manager in
  P_transform
    (Frontend_utils.make_transform
       ~print_out:Acids_interval.print_file
       "intervals"
       type_file)


