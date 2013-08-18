let node convo (c0, c1, c2) = (c0 + c1 + c2) / 3

let node convolution (p0, p1, p2) = (convo p0, convo p1, convo p2)

(* horizontal filter *)
let pword hf = ([true false]^2 false^2 true false^2)

@max_burst{1000}
let node horizontal_filter (p :: 'a on (9)) = o where
  rec p0 = p fby p1
  and p1 = p fby p2
  and p2 = p
  and o = (convolution (p0, p1, p2)) when hf

(* vertical sliding window *)
let pword first_sd_line = true^720(false)
let pword first_line_of_img = (true^720 false^{720 * 1079})
let pword last_line_of_img = (false^{720 * 1079} true^720)

let node my_fby_sd_line (p1, p2) =
  merge first_sd_line (p1 when first_sd_line) (buffer p2)

@max_burst{1000}
let node reorder (p :: 'a on (720)) = ((p0, p1, p2) :: 'a1) where
  rec p0 = if valof first_line_of_img then p1 else my_fby_sd_line (p1, p1)
  and p1 = buffer p
  and p2 = if valof last_line_of_img
           then p1
           else (p when (first_sd_line = false))

(* vertical filter *)
let pword vf = ([true^720 false^720]^2 false^720 true^720 false^1440 true^720)

@max_burst{10000}
let node vertical_filter p = o where
    rec (p0, p1, p2) = reorder p
    and o = convolution (p0, p1, p2) when vf

(* downscaler *)
@max_burst{10000} @max_int{1000000} @k'{2160}
let node downscaler p = vertical_filter (horizontal_filter p)

(* picture in picture *)
let pword incrust_end =
    (false^{1920 * (1080 - 480)} [false^1200 true^720]^480)

@max_burst{100000} @max_int{1000000}
let node picture_in_picture (p1, p2) = o where
    rec small = buffer (downscaler p1)
    and big = p2 when (incrust_end = false)
    and o = merge incrust_end small big
