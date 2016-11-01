let print_prod fmt () =
  if !Options.pp_unicode
  then Format.fprintf fmt "\xC3\x97"
  else Format.fprintf fmt "*"

let print_fun fmt () =
  if !Options.pp_unicode
  then Format.fprintf fmt "\xE2\x86\x92"
  else Format.fprintf fmt "->"

let print_mod fmt () =
  if !Options.pp_unicode
  then Format.fprintf fmt "\xE2\x80\xA2"
  else Format.fprintf fmt "%@"
