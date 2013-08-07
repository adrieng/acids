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

(** {2 Type definitions} *)

type word =
  {
    desc : (Int.t * Int.t) list;
    nbones : Int.t;
    size : Int.t;
  }

type pword = { u : word; v : word; }

(** {2 Printing} *)

let print_word fmt w =
  let print fmt (i, k) =
    if k = Int.one
    then Int.print fmt i
    else Format.fprintf fmt "%a^%a" Int.print i Int.print k
  in
  Format.fprintf fmt "@[%a@]" (Utils.print_list_r print "") w.desc

let print_pword fmt { u = u; v = v; } =
  Format.fprintf fmt "%a%s(%a)"
    print_word u
    (if u.size <> Int.zero then " " else "")
    print_word v

(** {2 Low-level functions on words} *)

let empty =
  {
    desc = [];
    nbones = Int.zero;
    size = Int.zero;
  }

let push i k w =
  let open Int in
  if k = zero then w
  else
    let desc =
      match w.desc with
      | (i', k') :: desc when i = i' ->
        (i, k + k') :: desc
      | _ -> (i, k) :: w.desc
    in
    {
      desc = desc;
      nbones = w.nbones + i * k;
      size = w.size + k;
    }

let rev w = { w with desc = List.rev w.desc; }

let pop w =
  let open Int in
  assert (w.size >= one);
  match w.desc with
  | [] -> assert false
  | (i, k) :: desc ->
    let w_rest =
      {
        desc = desc;
        nbones = w.nbones - i * k;
        size = w.size - k;
      }
    in
    i, k, w_rest

let pop_1 w =
  let open Int in
  assert (w.size >= one);
  match w.desc with
  | [] -> assert false
  | (i, k) :: desc ->
    let w_rest =
      {
        desc = if k > one then (i, k - one) :: desc else desc;
        nbones = w.nbones - i;
        size = w.size - one;
      }
    in
    i, w_rest

let unfold_max w1 w2 =
  let i1, k1, w1 = pop w1 in
  let i2, k2, w2 = pop w2 in
  let k = min k1 k2 in
  Int.(i1, i2, k, push i1 (k1 - k) w1, push i2 (k2 - k) w2)

let take n w =
  let open Int in
  assert (n <= w.size);
  let rec walk n acc w =
    if n = zero then acc, w
    else
      let i, k, w = pop w in
      let m = min n k in
      walk (n - m) (push i m acc) (push i (k - m) w)
  in
  let w_pref, w = walk n empty w in
  rev w_pref, w

(** {2 High-level functions on words} *)

let singleton i =
  {
    desc = [(i, Int.one)];
    nbones = i;
    size = Int.one;
  }

let concat w1 w2 =
  let add acc (i, k) = push i k acc in
  List.fold_left add w2 (List.rev w1.desc)

let power w i =
  let rec walk acc i =
    if Int.(i = one)
    then acc
    else walk (concat w acc) (Int.pred i)
  in
  if Int.(i = zero) then empty else walk w i

let size w = w.size

let nbones w = w.nbones

let rec ones_word acc w i =
  let open Int in
  assert (i >= zero);
  assert (i <= w.size);
  if i = zero then acc
  else
    let b, k, w = pop w in
    let m = min i k in
    let acc = acc + b * m in
    ones_word acc w (i - m)

let iof_word w j =
  let open Int in

  let rec iof_word acc w j =
    assert (j >= one && j <= w.nbones);
    let b, k, w = pop w in
    if j > b * k
    then iof_word (acc + k) w (j - b * k)
    else acc + div_b1 j b
  in

  if j = zero then zero else iof_word Int.one w j

let print_iof_list fmt iof_l =
  let print_couple fmt (j, i) =
    Format.fprintf fmt "(%a, %a)"
      Int.print j
      Int.print i
  in
  Format.fprintf fmt "@[[%a]@]"
    (Utils.print_list_r print_couple ",") iof_l

let debug = false

let make_word_alap ~max_burst ~size ~nbones iof =
  let open Int in
  if debug
  then
    Format.eprintf
      "@[<hv 2>make_word_alap:@ max_burst = %a,@ size = %a,@ nbones = %a,@ iof = %a@]@."
      print max_burst
      print size
      print nbones
      print_iof_list iof
  ;

  assert (nbones <= max_burst * size);
  assert (of_int (List.length iof) <= nbones);

  if size = zero then empty
  else
    (
      let iof = List.rev iof in

      let fill_head w n =
        assert (max_burst > zero);
        if w.size = zero then w, n
        else
          let b, k, w = pop w in
          assert (b >= zero && b <= max_burst);
          let m = min max_burst (b + n) in
          let d = m - b in
          push m one (push b (pred k) w), n - d
      in

      let add_alap size nbones w =
        assert (nbones >= zero && nbones <= size * max_burst);

        (* let w', nbones_r = fill_head w nbones in *)
        let bm = min max_burst nbones in
        let bm_k = if bm = zero then zero else nbones / bm in
        let rm = if bm = zero then zero else nbones mod bm in
        let rm_k = if rm = zero then zero else one in

        assert (bm_k + rm_k <= size);
        let z_k = size - bm_k - rm_k in

        let w' = push zero z_k (push rm rm_k (push bm bm_k w)) in
        assert (w'.nbones = w.nbones + nbones);
        assert (w'.size = w.size + size);
        w'
      in

      let rec make_iof prev_j prev_i acc iof =
        if debug
        then
          Format.eprintf
            "  @[<hv 2>make_iof:@ prev_j = %a,@ prev_i = %a,@ acc = [%a],@ iof = [%a]@."
            print prev_j
            print prev_i
            print_word acc
            print_iof_list iof
        ;
        assert (prev_i >= one && prev_i <= succ size);
        assert (prev_j >= one && prev_j <= succ nbones);
        match iof with
        | [] ->
          (* fill in the initial segment *)
          let prefix_size = pred prev_i in
          let remaining_ones = pred prev_j in
          let acc, remaining_ones = fill_head acc remaining_ones in
          add_alap prefix_size remaining_ones acc

        | (j, i) :: iof ->
          assert (prev_i >= i);
          assert (prev_j > j);

          (* segment size strictly between i and prev_i *)
          let segment_size = prev_i - i in
          (* number of ones strictly between j and prev_j *)
          let additional_nbones = prev_j - j - one in

          (* try to fill prev_j with additional ones *)
          let acc, remaining_nbones = fill_head acc additional_nbones in

          (* create the middle segment *)
          let segment_nbones = min (segment_size * max_burst) remaining_nbones in
          let acc = add_alap segment_size segment_nbones acc in

          (* put the I_w(j) = i one, filling in remaining nbones *)
          let acc, rem = fill_head acc one in
          assert (rem = zero);
          make_iof j i acc iof
      in
      let w = make_iof (succ nbones) (succ size) empty iof in
      w
    )

let make_word_alap ~max_burst ~size ~nbones iof =
  let w = make_word_alap ~max_burst ~size ~nbones iof in

  if debug
  then
    Format.eprintf
      "@[<hv 2>make_word_alap:@ max_burst = %a,@ size = %a,@ nbones = %a,@ iof = [@[%a@]]@ -> %a@]@."
      Int.print max_burst
      Int.print size
      Int.print nbones
      print_iof_list iof
      print_word w
  ;

  let check_iof (j, i) =
    if debug
    then
      Format.eprintf "(%a, %a) vs. I_[%a](%a) = %a@."
        Int.print j
        Int.print i
        print_word w
        Int.print j
        Int.print (iof_word w j)
    ;
    assert (Int.equal (iof_word w j) i);
  in

  assert (w.size = size);
  assert (w.nbones = nbones);
  assert (List.iter check_iof iof = ());

  w

let to_tree_word w =
  let open Tree_word in
  Concat (List.map (fun (i, k) -> Power (Leaf i, k)) w.desc)

(** {2 Low-level functions on pwords} *)

(** {2 Exported functions on pwords} *)

let make u v =
  assert (v.size > Int.zero);
  { u = u; v = v; }

let unit_pword = make empty (singleton Int.one)

let is_unit_word w =
  let rec walk desc =
    match desc with
    | [] -> true
    | (i, _) :: desc -> (i = Int.one) && walk desc
  in
  walk w.desc

let is_unit_pword { u = u; v = v; } =
  (u.size = Int.zero || is_unit_word u) && is_unit_word v

let ones w i =
  let open Int in
  assert (i >= zero);
  if i <= w.u.size
  then ones_word zero w.u i
  else
    let i = i - w.u.size in
    let nbones =
      let nth_iter = div_b1 i w.v.size in
      w.u.nbones + w.v.nbones * nth_iter
    in
    ones_word nbones w.v (mod_b1 i w.v.size)

let iof w j =
  let open Int in
  assert (j >= zero);
  assert (j <= w.u.nbones || w.v.nbones >= one);
  let r =
    if j <= w.u.nbones
    then iof_word w.u j
    else
      let j_v = j - w.u.nbones in
      let base_pos = w.u.size + w.v.size * Int.div_b1 j_v w.v.nbones in
      let j_v' = mod_b1 j_v w.v.nbones in
      base_pos + iof_word w.v j_v'
  in
  r

let lengthen_prefix { u = u; v = v; } n =
  let open Int in
  let period_count = n / v.size in
  let full_periods = power v period_count in
  let n = n mod v.size in
  let v_pref, v = take n v in
  make (concat (concat u full_periods) v_pref) (concat v v_pref)

let repeat_period w n = make w.u (power w.v n)

let on ({ u = u1; v = v1; } as p1) { u = u2; v = v2; } =
  let open Int in

  let u_size =
    if v1.nbones = zero then u1.size else max u1.size (iof p1 u2.size)
  in
  let v_size =
    if v1.nbones = zero then one
    else ((lcm v1.nbones v2.size) / v1.nbones) * v1.size
  in

  let rec sum_burst acc i u2 =
    if i = zero then acc, u2
    else if u2.size = zero then sum_burst acc i v2
    else
      let b, n, u2 = pop u2 in
      let m = min i n in
      sum_burst (acc + b * m) (i - m) (push b (n - m) u2)
  in

  let rec walk u1 u2 res n =
    if u1.size = zero then walk v1 u2 res n
    else if u2.size = zero then walk u1 v2 res n
    else if n = zero then u1, u2, rev res
    else
      let i, u1 = pop_1 u1 in
      let b, u2 = sum_burst zero i u2 in
      walk u1 u2 (push b one res) (pred n)
  in

  let r1, r2, u = walk u1 u2 empty u_size in
  let _, _, v = walk r1 r2 empty v_size in

  make u v

let rate p = Rat.make p.v.nbones p.v.size

let common_behavior_size p1 p2 =
  let open Int in
  max p1.u.size p2.u.size + lcm p1.v.size p2.v.size

let equal p1 p2 =
  p1 == p2
  || p1 = p2
  ||
    let rec walk w1 w2 n =
      let open Int in
      (n <= zero)
      ||
        if w1.size = zero then walk p1.v w2 n
        else if w2.size = zero then walk w1 p2.v n
        else
          (* TODO more efficient *)
          let b1, w1 = pop_1 w1 in
          let b2, w2 = pop_1 w2 in
          (b1 = b2) && walk w1 w2 (pred n)
    in
    walk p1.u p2.u (common_behavior_size p1 p2)

let common_behavior_nbones p1 p2 =
  let open Int in
  max p1.u.nbones p2.u.nbones + lcm p1.v.nbones p2.v.nbones

(* Check that forall i, O_p1(i) >= O_p2(i + delay) (with delay >= 0) *)
let precedes ?(delay = Int.zero) p1 p2 =
  let open Int in

  let max = common_behavior_nbones p1 p2 in

  assert (delay >= zero);
  assert (delay <= max);

  let rec walk w1 w2 o1 o2 j =
    if j > max then true
    else
      if w1.size = zero then walk p1.v w2 o1 o2 j
      else if w2.size = zero then walk w1 p2.v o1 o2 j
      else
        let b1, b2, k, w1, w2 = unfold_max w1 w2 in
        let o1' = o1 + b1 * k in
        let o2' = o2 + b2 * k in
        (o1' >= o2') && walk w1 w2 o1' o2' (j + k)
  in

  let o2 = ones p2 delay in
  let w2 =
    if delay < p2.u.size
    then
      let _, u = take delay p2.u in
      u
    else
      let shift = (delay - p2.u.size) mod p2.v.size in
      let _, v = take shift p2.v in
      v
  in
  walk p1.u w2 zero o2 zero

let synchro p1 p2 = Rat.(rate p1 = rate p2)

let adapt ?(delay = Int.zero) p1 p2 = synchro p1 p2 && precedes ~delay p1 p2

let to_tree_pword p =
  { Tree_word.u = to_tree_word p.u; Tree_word.v = to_tree_word p.v; }
