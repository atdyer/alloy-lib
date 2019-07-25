
module iter

pred loop2 [r: Int->Int, iter: Int->Int->Int] {
  #iter = #r                          -- same size as r
  iter.Int = r                        -- make left side = r
  c3[iter] = range[1, add[#r, 1]]     -- make right side = time stamps
  all i, i': r.Int,
      j, j': Int.r,
      t, t': range[1, add[#r, 1]] {
    i->j->t in iter and i'->j'->t' in iter and t < t' =>
      i <= i' and (i = i' => j < j')
  }
}

fun range [n: Int]: set Int {
  { i: Int | 0 <= i and i < n }
}

fun range [m, n: Int]: set Int {
  { i: Int | m <= i and i < n }
}

fun c1 [r: Int->Int->Int]: Int {   -- first column of a ternary relation
  r.Int.Int
}

fun c2 [r: Int->Int->Int]: Int {   -- second column of a ternary relation
  Int.(r.Int)
}

fun c3 [r: Int->Int->Int]: Int {   -- third column of a ternary relation
  Int.(Int.r)
}

pred show {
  let n = 3, a = 2, b = 4 |
    some iter: Int->Int->Int |
      loop2[{i: range[n], k: range[a, b]}, iter]
}

run show for 4 Int
