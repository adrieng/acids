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

let static sd_width = 720
let static sd_height = 480
let static hd_width = 1920
let static hd_height = 1080

(* vertical sliding window *)
let pword first_sd_line = true^{sd_width}(false)
let pword first_line_of_img =
    (true^{sd_width} false^{sd_width * (hd_height - 1)})
let pword last_line_of_img =
    (false^{sd_width * (hd_height - 1)} true^{sd_width})

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
let pword vf = ([true^{sd_width} false^{sd_width}]^2
                false^{sd_width}
                true^{sd_width}
                false^{sd_width * 2}
                true^{sd_width})

@max_burst{10000}
let node vertical_filter p = o where
    rec (p0, p1, p2) = reorder p
    and o = convolution (p0, p1, p2) when vf

(* downscaler *)
@max_burst{10000} @max_int{1000000} @k'{2160}
let node downscaler p = vertical_filter (horizontal_filter p)

(* picture in picture *)
let pword incrust_end =
    (false^{hd_width * (hd_height - sd_height)}
     [false^{hd_width - sd_width} true^{sd_width}]^{sd_height})

@max_burst{100000} @max_int{1000000}
let node picture_in_picture (p1, p2) = o where
    rec small = buffer (downscaler p1)
    and big = p2 when (incrust_end = false)
    and o = merge incrust_end small big
