(* Copyright (C) Adrien Guatto <adrien.guatto@laposte.net> 2012
 *
 * This file is part of nsched.
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

(** {1 Preliminary definitions} *)

type transform_name = string

exception Evaluation_terminated

(** {1 Compilation context} *)

type attr = string

type ctx

val make_ctx :
  ?serialize_transforms:transform_name list ->
  ?stop_after:transform_name option ->
  current_file:string ->
  error_is_internal:(exn -> bool) ->
  print_error:(ctx -> Format.formatter -> exn -> unit) ->
  unit ->
  ctx

val print_ctx : Format.formatter -> ctx -> unit

val ctx_current_file : ctx -> string

val ctx_current_dir : ctx -> string

val ctx_set_attr : ctx -> attr * bool -> ctx
val ctx_get_attr : ctx -> attr -> bool

val print_debug
  : ctx -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit

(** {1 Properties and combinators} *)

type 'a prop
val prop : (ctx -> 'a -> string option) -> 'a prop
val none : 'a prop
val both : 'a prop -> 'a prop -> 'a prop
val either : 'a prop -> 'a prop -> 'a prop
val all_of : ('a prop) list -> 'a prop

(** {1 Transforms} *)

type ('i, 'o) transform

val make_transform :
  ?assume:'a prop ->
  ?guarantee:'b prop ->
  ?print_in:(Format.formatter -> 'a -> unit) ->
  ?print_out:(Format.formatter -> 'b -> unit) ->
  transform_name ->
  (ctx -> 'a -> ctx * 'b) ->
  ('a, 'b) transform

(** {1 Passes} *)

type _ pass =
  | P_transform : ('i, 'o) transform -> ('i -> 'o) pass
  | P_comp : ('a -> 'b) pass * ('b -> 'c) pass -> ('a -> 'c) pass
  | P_sel : (ctx -> ('a -> 'b) pass) -> ('a -> 'b) pass

val (+>+) : ('a -> 'b) pass -> ('b -> 'c) pass -> ('a -> 'c) pass

val eval : ('a -> 'b) pass -> ctx -> 'a -> (ctx * 'b) option

val eval_to_completion : ('a -> 'b) pass -> ctx -> 'a -> bool

val identity_pass : unit -> ('a -> 'a) pass

val make_selection_pass_by_attr :
  attr -> ('a -> 'b) pass -> ('a -> 'b) pass -> ('a -> 'b) pass
