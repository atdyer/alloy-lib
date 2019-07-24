
pred increment_ranges [IA, IA': seq Int] {
//  some ia: Int->Int->Int {
//    -- ia = (t, IA)
//    ia[0] = zeros[#IA]
//    let itertab = ... {
//      all it: range[#itertab] {
//      }
//    }
//  }
}

pred gentab [IA: seq Int, tab: Int->Int->Int] {
  tab[0] = 0->IA[0]
  c2[tab] = evens[#IA]
  c1[tab] = range[#tab]
  all i: range[(#tab).sub[1]] {
    (tab[i.next].Int = tab[i].Int) or
    (tab[i.next].Int = (tab[i].Int).add[2])
  }
  all i: Int {
    i in c2[tab] => {
      let s = IA[i], t = IA[i.add[1]] {
        tab[Int][i] = range[s, t]
      }
    }
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
--  count = #{ i: dom[s] | rem[s[i], 2] = 0 }
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

run {
  some IA, IA': seq Int, tab: Int->Int->Int {
    #IA = 4
    IA[0] = 0
    IA[1] = 3
    IA[2] = 1
    IA[3] = 2
--    increment_ranges[IA, IA']
    gentab[IA, tab]
  }
} for 6 seq
