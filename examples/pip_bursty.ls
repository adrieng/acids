let node convo (c0, c1, c2) = (c0 + c1 + c2) / 3

let node convolution (p0, p1, p2) = (convo p0, convo p1, convo p2)

@max_burst{1000}
let node horizontal_filter (p :: 'a on (9)) = o where
  rec p0 = p fby p1
  and p1 = p fby p2
  and p2 = p
  and o =
    (convolution (p0, p1, p2)) when ({true false}^2 false^2 true false^2)

let node my_fby_sd_line (p1, p2) =
  merge true^720(false) (p1 when true^720 (false)) (buffer p2)

@max_burst{1000}
let node reorder (p :: 'a1 on (720)) = ((p0, p1, p2) :: 'a) where
  rec p0 = if valof true^720(false) then p1 else my_fby_sd_line (p1, p2)
  and p1 = buffer p
  and p2 = if valof <(false^first_lines_count true^720)>
           then p1
           else (p when false^720(true))
  and first_lines_count = 720 * 1079

@max_burst{10000}
let node vertical_filter p = o where
    rec (p0, p1, p2) = reorder p
    and o =
        convolution (p0, p1, p2)
        when ({true^720 false^720}^2 false^720 true^720 false^1440 true^720)

@max_burst{10000} @max_int{1000000} @k'{2160}
let node downscaler p = vertical_filter (horizontal_filter p)

@max_burst{100000} @max_int{1000000}
let node picture_in_picture (p1, p2) =
  o where
    rec small = buffer (downscaler p1)
    and big = p2 when <(true^non_sd_lines {true^1200 false^720}^480)>
    and o = merge <(true^non_sd_lines {true^1200 false^720}^480)> big small
    and non_sd_lines = 1920 * (1080 - 480)
