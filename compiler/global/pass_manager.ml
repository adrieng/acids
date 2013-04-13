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

(** {1 Compiler context} *)

type attr = string

type ctx = {
  ctx_current_file : string;
  ctx_stop_after : transform_name option;
  ctx_serialize_transforms : transform_name list;
  ctx_error_is_internal : exn -> bool;
  ctx_print_error : ctx -> Format.formatter -> exn -> unit;
  ctx_attr : bool Utils.String_map.t;
}

let make_ctx
    ?(serialize_transforms = [])
    ?(stop_after = None)
    ~current_file ~error_is_internal ~print_error
    ()
    =
  {
    ctx_current_file = current_file;
    ctx_serialize_transforms = serialize_transforms;
    ctx_stop_after = stop_after;
    ctx_error_is_internal = error_is_internal;
    ctx_print_error = print_error;
    ctx_attr = Utils.String_map.empty;
  }

let print_ctx fmt ctx =
  Format.fprintf fmt "@[<v 2>Compiler context:@\n";

  Format.fprintf fmt "stop after: %a@\n"
    (Utils.print_opt ~s:"." Utils.print_string) ctx.ctx_stop_after;
  Format.fprintf fmt "serialize transforms: [@[%a@]]@\n"
    (Utils.print_list_r Utils.print_string ",") ctx.ctx_serialize_transforms;

  Format.fprintf fmt "@[<v 2>attributes:";
  Utils.String_map.iter
    (fun id b -> Format.fprintf fmt "@ %s = %b;" id b)
    ctx.ctx_attr;
  Format.fprintf fmt "@]";

  Format.fprintf fmt "@]"

let ctx_current_file ctx = ctx.ctx_current_file

let ctx_current_dir ctx = Filename.dirname (ctx_current_file ctx)

let ctx_set_attr ctx (attr, b) =
  { ctx with ctx_attr = Utils.String_map.add attr b ctx.ctx_attr; }

let ctx_get_attr ctx attr =
  try Utils.String_map.find attr ctx.ctx_attr
  with Not_found -> false

let debug ctx = ctx_get_attr ctx "debug"

let print_debug ctx p fmt x = if debug ctx then p fmt x

let check_transforms ctx = ctx_get_attr ctx "check" || ctx_get_attr ctx "debug"

(** {1 Properties and combinators} *)

type 'a prop =
    ctx -> 'a -> string option (* None = ok, Some reason = bad for [reason] *)

let prop f ctx x = f ctx x

let none _ _ = None

let both p1 p2 ctx a =
  match p1 ctx a with
  | None -> p2 ctx a
  | Some reason -> Some reason

let either p1 p2 ctx a =
  match p1 ctx a, p2 ctx a with
  | None, _ | _, None -> None
  | Some reason, Some reason' -> Some ("neither " ^ reason ^ " nor " ^ reason')

let all_of p_l = List.fold_left both none p_l

(** {1 Passes} *)

type ('i, 'o) transform =
  {
    t_name : transform_name;

    t_desc : ctx -> 'i -> ctx * 'o;

    t_assume : 'i prop;
    t_guarantee : 'o prop;

    t_print_input : (Format.formatter -> 'i -> unit) option;
    t_print_output : (Format.formatter -> 'o -> unit) option;
    t_ext : string;
  }

let make_transform
    ?(assume = none) ?(guarantee = none) ?(ext = ".log")
    ?print_in ?print_out
    name desc
    =
  {
    t_name = name;
    t_desc = desc;
    t_assume = assume;
    t_guarantee = guarantee;
    t_print_input = print_in;
    t_print_output = print_out;
    t_ext = ext;
  }

type _ pass =
  | P_transform : ('i, 'o) transform -> ('i -> 'o) pass
  | P_comp : ('a -> 'b) pass * ('b -> 'c) pass -> ('a -> 'c) pass
  | P_sel : (ctx -> ('a -> 'b) pass) -> ('a -> 'b) pass

let (+>+) p1 p2 = P_comp (p1, p2)

type reason = string

type backtrace = string

type eval_error =
  | Assumption_violated of reason
  | Guarantee_violated of reason
  | Other_exception of exn * backtrace

let print_error fmt (transform_name, ctx, error) =
  match error with
  | Assumption_violated reason ->
    Format.fprintf fmt "[%s] assumption violated: %s" transform_name reason
  | Guarantee_violated reason ->
    Format.fprintf fmt "[%s] guarantee violated: %s" transform_name reason
  | Other_exception (exn, bt) ->
    if ctx.ctx_error_is_internal exn
    then
      (
        Format.fprintf fmt
          "[%s] internal compiler error in file %s:@ %a@\n%s@\n"
          transform_name
          ctx.ctx_current_file
         (ctx.ctx_print_error ctx) exn
          bt;
       Format.fprintf fmt "%a" print_ctx ctx
      )
    else Format.fprintf fmt "%a" (ctx.ctx_print_error ctx) exn

exception Eval_error of transform_name * ctx * eval_error

let transform_error transform_name ctx exn =
  let bt = Printexc.get_backtrace () in
  raise (Eval_error (transform_name, ctx, Other_exception (exn, bt)))

let assumption_violated transform_name ctx reason =
  raise (Eval_error (transform_name, ctx, Assumption_violated reason))

let guarantee_violated transform_name ctx reason =
  raise (Eval_error (transform_name, ctx, Guarantee_violated reason))

let serialize_transform ctx t y =
  match t.t_print_output with
  | None -> Format.printf "[%s] could not serialize (no printer)@." t.t_name
  | Some print ->
    let t_name = Str.global_replace (Str.regexp " ") "_" t.t_name in
    let fn =
      Printf.sprintf
        "%s.log.%s.%s"
        (Filename.chop_extension (ctx_current_file ctx))
        t_name
        t.t_ext
    in
    if debug ctx
    then Format.printf "(* [%s] serialized to %s *)@." t.t_name fn;
    let oc = open_out fn in
    let fmt = Format.formatter_of_out_channel oc in
    Format.fprintf fmt "%a@?" print y;
    close_out oc

let print_value p fmt x =
  match p with
  | None -> ()
  | Some p -> p fmt x

let rec eval : type i o. (i -> o) pass -> ctx -> i -> ctx * o =
  fun p ctx x ->
    match p with
    | P_transform t ->
      (
        if check_transforms ctx
        then
          Utils.iter_opt (assumption_violated t.t_name ctx) (t.t_assume ctx x);
      );

      if debug ctx then Format.printf "(* [%s] running *)@\n" t.t_name;

      Format.printf "@?";
      let start_time = Unix.gettimeofday () in
      let ctx, y =
        try t.t_desc ctx x with exn -> transform_error t.t_name ctx exn
      in
      let stop_time = Unix.gettimeofday () in

      if List.mem t.t_name ctx.ctx_serialize_transforms
      then serialize_transform ctx t y;

      if debug ctx
      then
        (
          Format.printf "(* [%s] finished, %.2f seconds *)@\n"
            t.t_name
            (stop_time -. start_time);
          Format.printf "%a@\n" (print_value t.t_print_output) y;
        );

      Format.printf "@?";

      (
        if check_transforms ctx
        then
          Utils.iter_opt
            (guarantee_violated t.t_name ctx) (t.t_guarantee ctx y);
      );

      if Some t.t_name = ctx.ctx_stop_after then raise Evaluation_terminated;

      ctx, y

    | P_comp (p1, p2) ->
      let ctx, x = eval p1 ctx x in
      eval p2 ctx x
    | P_sel sel ->
      eval (sel ctx) ctx x

let eval p ctx x =
  let rec aux p ctx x =
    if debug ctx
    then Format.printf "(*@[@\n%a@]@\n*)@\n" print_ctx ctx;

    try Some (eval p ctx x)
    with Eval_error (transform_name, ctx, err) ->
      Format.eprintf "%a@." print_error (transform_name, ctx, err);
      (
        match err with
        | Other_exception (exn, _) when ctx.ctx_error_is_internal exn ->
          if not (debug ctx)
          then
            (
              Format.eprintf "Rerunning in debug mode.@.";
              ignore (aux p (ctx_set_attr ctx ("debug", true)) x)
            );
          Compiler.internal_error "uncaught exception"
        | _ ->
          None
      )
  in
  aux p ctx x

let eval_to_completion p ctx x =
  try
    match eval p ctx x with
    | Some _ -> true
    | None -> false
  with Evaluation_terminated -> true

let identity_pass () =
  let id ctx x = ctx, x in
  P_transform (make_transform "identity pass" id)

let make_selection_pass_by_attr attr p1 p2 =
  P_sel (fun ctx -> if ctx_get_attr ctx attr then p1 else p2)
