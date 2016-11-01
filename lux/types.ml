type base_typ =
| Bool
| Char
| Int
| Float

type ty =
| Unit
| Stream of base_typ
| Prod of ty * ty
| Fun of ty * ty
| Box of Pword.pword * ty

let string_of_base_typ bty =
  match bty with
  | Bool -> "bool"
  | Char -> "char"
  | Int -> "int"
  | Float -> "float"

let print_base_typ fmt bty =
  Format.fprintf fmt "%s" (string_of_base_typ bty)

let rec print_ty fmt ty =
  let in_pp_box f fmt x =
    Format.fprintf fmt "@[%a@]" f x
  in

  let in_pp_par f fmt x =
    Format.fprintf fmt "(%a)" (in_pp_box f) x
  in

  let rec print_prod_ty fmt ty =
    match ty with
    | Unit | Stream _ ->
      print_ty fmt ty
    | Prod (ty1, ty2) ->
      Format.fprintf fmt "%a@ %a %a"
        print_prod_ty ty1
        Pp.print_prod ()
        print_prod_ty ty2
    | Fun _ ->
      in_pp_par print_fun_ty fmt ty
    | Box _ ->
      in_pp_box print_box_ty fmt ty

  and print_fun_ty fmt ty =
    match ty with
    | Unit | Stream _ ->
      print_ty fmt ty
    | Prod _ ->
      in_pp_box print_prod_ty fmt ty
    | Fun ((Unit | Stream _ | Box _ | Prod _) as ty1, ty2) ->
      Format.fprintf fmt "%a@ %a %a"
        (in_pp_box print_ty) ty1
        Pp.print_fun ()
        print_fun_ty ty2
    | Fun ((Fun _) as ty1, ty2) ->
      Format.fprintf fmt "%a@ %a %a"
        (in_pp_par print_fun_ty) ty1
        Pp.print_fun ()
        print_fun_ty ty2
    | Box _ ->
      in_pp_box print_box_ty fmt ty

  and print_box_ty fmt ty =
    match ty with
    | Unit | Stream _ ->
      print_ty fmt ty
    | Prod _ ->
      in_pp_par print_prod_ty fmt ty
    | Fun _ ->
      in_pp_par print_fun_ty fmt ty
    | Box (p, ty) ->
      Format.fprintf fmt "%a%a@ %a"
        Pp.print_mod ()
        Pword.print_pword p
        print_box_ty ty
  in
  match ty with
  | Unit ->
    Format.fprintf fmt "unit"
  | Stream bty ->
    Format.fprintf fmt "stream %a" print_base_typ bty
  | Prod _ ->
    in_pp_box print_prod_ty fmt ty
  | Fun _ ->
    in_pp_box print_fun_ty fmt ty
  | Box _ ->
    in_pp_box print_box_ty fmt ty

let rec normalize ty =
  let box p ty =
    if Pword.is_unit_pword p then ty else Box (p, ty)
  in

  let rec push p ty =
    match ty with
    | Unit ->
      Unit
    | Stream _ ->
      box p ty
    | Prod (ty1, ty2) ->
      Prod (push p ty1, push p ty2)
    | Fun (ty1, ty2) ->
      box p (Fun (normalize ty1, normalize ty2))
    | Box (p', ty) ->
      push (Pword.on p p') ty
  in

  push Pword.unit_pword ty
