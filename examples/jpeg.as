let node zigzag x = o where
    rec (x0, x1, x2, x3, x4, x5, x6, x7, x8) =
        split x with (0 1 2 3 4 5 6 7 8) by (0, 1, 2, 3, 4, 5, 6, 7, 8)
    and o =
        merge (0 1 3 6 4 2 5 7 8) with
              | 0 -> buffer x0
              | 1 -> buffer x1
              | 2 -> buffer x2
              | 3 -> buffer x3
              | 4 -> buffer x4
              | 5 -> buffer x5
              | 6 -> buffer x6
              | 7 -> buffer x7
              | 8 -> buffer x8
        end
