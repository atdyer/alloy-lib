
pred increment_ranges [IA, IA': seq Int] {
  some ia: Int->Int->Int, iter: Int->Int->Int {
    ia[0] = zeros[max[IA[Int]]]
    loop2[{i: evens[#IA], k: range[IA[i], IA[i.add[1]]]}, iter]
    all i: evens[#IA] {
      all k: range[IA[i], IA[i.add[1]]] {
        let t = iter[i][k],
            t' = t.add[1],
            v = ia[t][k],
            v' = v.add[1] {
          ia[t'] = ia[t] ++ k->v'
        }
      }
    }
    IA' = ia[#iter]
  }
}

run {
  some IA, IA': seq Int {
    #IA = 4
    IA[0] = 0
    IA[1] = 3
    IA[2] = 1
    IA[3] = 2
    increment_ranges[IA, IA']
  }
}

run {
  some IA, IA': seq Int {
    #IA = 6
    IA[0] = 0
    IA[1] = 3
    IA[2] = 1
    IA[3] = 3
    IA[4] = 2
    IA[5] = 3
    increment_ranges[IA, IA']
  }
} for 6 seq

pred loop2 [r: Int->Int, iter: Int->Int->Int] {
  #iter = #r                          -- same size as r
  iter.Int = r                        -- make left side = r
  c3[iter] = range[#r]                -- make right side = time stamps
  all i, i': r.Int,
      j, j': Int.r,
      t, t': range[#r] {
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

fun zeros [n: Int]: seq Int {
  range[n] -> 0
}

fun evens[n: Int]: set Int {
  { i: range[n] | all k: i | rem[k, 2] = 0 }
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
