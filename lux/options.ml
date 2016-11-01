let yes_no r s =
  match s with
  | "yes" ->
    r := true
  | "no" ->
    r := false
  | _ ->
    invalid_arg ("yes_no: yes or no expected, got " ^ s)

let pp_unicode = ref true
