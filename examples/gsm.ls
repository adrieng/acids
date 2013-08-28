let node xor ((a :: 'a), (b :: 'a)) = (true :: 'a) (* TODO *)

let node split_speech x = split x with (0^50 1^132 2^78) by (0, 1, 2)

let node join_50_3 (x, r0, r1, r2) =
    merge (0^50 1 2 3) with
      | 0 -> x
      | 1 -> r0
      | 2 -> r1
      | 3 -> r2
    end

let node div_X3_X1_1 x = (u0, u1, u2) where
    rec u0 = false fby xor(x, u2)
    and u1 = false fby xor(u0, u2)
    and u2 = false fby u1

let node cyclic_encoding x = y where
    rec (u0, u1, u2) = div_X3_X1_1 x
    and y = join_50_3 (x,
                       buffer (u0 when (false^49 true)),
                       buffer (u1 when (false^49 true)),
                       buffer (u2 when (false^49 true)))

let node multiplexer (x1, x2) = merge (true false) x1 x2

let node convolutional_encoding x = y where
  rec x' = merge (true^185 false^4) x false
  and u4 = merge true^4(false) false (buffer x')
  and u1 = u4 when false^3(true)
  and u2 = u4 when false^2(true)
  and u3 = u4 when false^1(true)
  and x1 = xor (xor (xor (x', buffer u1), buffer u3), buffer u4)
  and x2 = xor (xor (x', buffer u3), buffer u4)
  and y = multiplexer (buffer x1, buffer x2)

(*
let node convolutional_encoding x = y where
    rec x' = merge (true^185 false^4) x false
    and u1 = false fby x'
    and u2 = false fby u1
    and u3 = false fby u2
    and u4 = false fby u3
    and x1 = xor (xor (xor (x', u1), u3), u4)
    and x2 = xor (xor (x', u3), u4)
    and y = multiplexer (x1, buffer x2)
*)

let node encode_without_buffer x = y where
    rec (x_Ia, x_Ib, x_II) = split_speech x
    and y1 = cyclic_encoding x_Ia
    and y1_x_Ib = merge (true^53 false^132) y1 x_Ib
    and y2 = convolutional_encoding y1_x_Ib
    and y = merge (true^378 false^78) y2 x_II
