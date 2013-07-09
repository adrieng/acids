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
  assert (i <= w.size);
  if i = zero then acc
  else
    let b, k, w = pop w in
    let m = min i k in
    let acc = acc + b * m in
    ones_word acc w (i - m)

let iof_word w j =
  let rec iof_word acc w j =
    let open Int in
    assert (j >= one && j <= w.nbones);
    let b, k, w = pop w in
    if j > b * k
    then iof_word (acc + k) w (j - b * k)
    else acc + div_b1 j b
  in
  iof_word Int.one w j

let print_iof_list fmt iof_l =
  let print_couple fmt (j, i) =
    Format.fprintf fmt "(%a, %a)"
      Int.print j
      Int.print i
  in
  Format.fprintf fmt "@[[%a]@]"
    (Utils.print_list_r print_couple ",") iof_l

let print_iofb_list fmt iofb_l =
  let print_triple fmt (j, i, b) =
    Format.fprintf fmt "(%a, %a, %a)"
      Int.print j
      Int.print i
      Int.print b
  in
  Format.fprintf fmt "@[[%a]@]"
    (Utils.print_list_r print_triple ",") iofb_l

let make_word_alap ~max_burst ~size ~nbones iof =
  let open Int in

  assert (nbones <= max_burst * size);
  assert (of_int (List.length iof) <= nbones);

  if size = zero then empty
  else
    (
      (* First pass: find ones at the same index and build bursts out of them *)
      let iof =
        let rec make_iof_burst acc iof =
          match iof with
          | [] -> acc
          | (j, i) :: iof ->
            let burst, iof =
              let rec find_burst burst iof =
                match iof with
                | [] -> burst, iof
                | (j', i') :: iof' ->
                  assert (i' >= i);
                  assert (j' >= j);
                  if i' > i then burst, iof else find_burst (succ burst) iof'
              in
              find_burst one iof
            in
            make_iof_burst ((j, i, burst) :: acc) iof
        in

        make_iof_burst [] iof
      in

      (** [push_segment_alap b prefix_size additional_nbones w] adds a word [w']
          of size [suffix_size + 1] to [w] with [additional_nbones] ones inside,
          such that [w'] begins with an integer greater than [b]. It also
          returns [b'] which is [b] plus the amount of [additional_nbones] added
          to it. *)
      let push_segment_alap b suffix_size additional_nbones w =

        assert (suffix_size >= zero);
        assert (additional_nbones >= zero);
        assert (b >= zero && b <= max_burst);
        assert (b + additional_nbones <= max_burst * succ suffix_size);

        (* First fill the suffix *)
        let bm = min max_burst additional_nbones in
        let bm_k =
          let bm_k = if bm = zero then zero else additional_nbones / bm in
          if bm_k > suffix_size then suffix_size else bm_k
        in

        (* (including some residual int if max_burst does not divide additional_nbones *)
        let rm = if bm = zero then zero else additional_nbones mod bm in
        let rm_k = if rm = zero || bm_k = suffix_size then zero else one in
        let remaining_nbones = additional_nbones - bm * bm_k - rm * rm_k in

        assert (bm_k + rm_k <= suffix_size);

        (* Fill the rest of the suffix with zeroes *)
        let z_k = suffix_size - bm_k - rm_k in

        (* Finally fill b *)

        let b' = min max_burst (b + remaining_nbones) in

        assert (bm * bm_k + rm * rm_k + (b' - b) = additional_nbones);

        (* b'^one 0^z_k rm^rm_k bm^bm_k *)
        push b' one (push zero z_k (push rm rm_k (push bm bm_k w))),
        b'
      in

      let rec make_iof prev_j prev_i iof w =
        (* Format.eprintf *)
        (*   "@[<hv 2>make_iof:@ prev_j = %a,@ prev_i = %a,@ iof = %a,@ w = %a@]@." *)
        (*   print prev_j *)
        (*   print prev_i *)
        (*   print_iofb_list iof *)
        (*   print_word w; *)

        match iof with
        | [] ->
          (* Here we are creating the initial segment, if any *)
          if prev_i = one then w
          else
            let initial_size = prev_i - one in
            let initial_nbones = prev_j - one in
            let w, _ =
              push_segment_alap zero (pred initial_size) initial_nbones w
            in
            w

        | (j, i, b) :: iof ->
          assert (prev_i > i);
          assert (prev_j > j + b - one);
          let suffix_size = prev_i - i - one in
          let additional_nbones = prev_j - j - b in

          let w, b =
            push_segment_alap b suffix_size additional_nbones w
          in

          make_iof (j + b - one) i iof w
      in
      (* Format.eprintf "-> %a, %a@." print nbones print size; *)

      let w = make_iof (succ nbones) (succ size) iof empty in
      w
    )

let make_word_alap ~max_burst ~size ~nbones iof =
  (* Format.eprintf "@.@.@."; *)
  let w = make_word_alap ~max_burst ~size ~nbones iof in

  (* Format.eprintf *)
  (*   "@[make_word_alap:@ max_burst = %a,@ size = %a,@ nbones = %a,@ iof = [@[%a@]]@ -> %a@]@." *)
  (*   Int.print max_burst *)
  (*   Int.print size *)
  (*   Int.print nbones *)
  (*   print_iof_list iof *)
  (*   print_word w *)
  (* ; *)

  let check_iof (j, i) =
    (* Format.eprintf "(%a, %a) vs. I_[%a](%a) = %a@." *)
    (*   Int.print j *)
    (*   Int.print i *)
    (*   print_word w *)
    (*   Int.print j *)
    (*   Int.print (iof_word w j) *)
    (* ; *)
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
  assert (v.size <> Int.zero);
  { u = u; v = v; }

let ones w i =
  let open Int in
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
  let v_pref, v = take n v in
  make (concat u v_pref) (concat v v_pref)

let repeat_period w n = make w.u (power w.v n)

let on ({ u = u1; v = v1; } as p1) { u = u2; v = v2; } =
  let open Int in

  let u_size =
    if v1.nbones = zero then u1.size else max u1.size (iof p1 v1.size)
  in
  let v_size =
    if v1.nbones = zero then one
    else ((lcm v1.nbones v2.size) / v1.nbones) * v1.size
  in

  let rec walk u1 u2 res n =
    if u1.size = zero then walk v1 u2 res n
    else if u2.size = zero then walk u1 v2 res n
    else if n = zero then u1, u2, rev res
    else
      let i, u1 = pop_1 u1 in
      let u2_pref, u2 = take i u2 in
      walk u1 u2 (push u2_pref.nbones one res) (n - one)
  in

  let r1, r2, u = walk u1 u2 empty u_size in
  let _, _, v = walk r1 r2 empty v_size in
  make u v

let rate p = Rat.make p.v.nbones p.v.size

let common_behavior p1 p2 =
  let open Int in
  max p1.u.size p2.u.size + lcm p1.u.nbones p2.u.nbones

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
          (* This is correct since words are always maximally factored *)
          let b1, k1, w1 = pop w1 in
          let b2, k2, w2 = pop w2 in
          (b1 = b2) && (k1 = k2) && walk w1 w2 (n - k1)
    in
    walk p1.u p2.u (common_behavior p1 p2)

let precedes ?(strict = false) p1 p2 =
  let open Int in

  let max = common_behavior p1 p2 in

  let rec walk w1 w2 o1 o2 j =
    if j > max then true
    else
      if w1.size = zero then walk p1.v w2 o1 o2 j
      else if w2.size = zero then walk w1 p2.v o1 o2 j
      else
        let b1, b2, k, w1, w2 = unfold_max w1 w2 in
        let o1' = o1 + b1 * k in
        let o2' = o2 + b2 * k in
        let prec = o1' >= o2' && (not strict || o1 >= o2') in
        prec && walk w1 w2 o1' o2' (j + k)
  in
  walk p1.u p2.u zero zero zero

let synchro p1 p2 = Rat.(rate p1 = rate p2)

let adapt p1 p2 = synchro p1 p2 && precedes p1 p2

let to_tree_pword p =
  { Tree_word.u = to_tree_word p.u; Tree_word.v = to_tree_word p.v; }
