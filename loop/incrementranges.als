sig LS {
  i, k: Int
}

pred init [ls: LS] {
  ls.i = 0
  ls.k = 0
}

pred nxt [ls, ls': LS, ia, ia': seq Int] {
  ls'.i = ls.i.add[1]
}

pred test [ia: seq Int] {
  #ia = 2
  ia[0] = 1
  ia[1] = 2
}

pred increment[ia, ia': seq Int] {
  #ia' = 
  some is: LS, sa: seq LS {
    sa[0] = is
    init[is]
    all i: range[#sa.butlast] {
      nxt[sa[i], sa[i.add[1]]]
    }
  }
}

run {
  some ia, ia': seq Int | test[ia] and increment[ia, ia']
}

fun range [n: Int]: set Int {
  { i: Int | 0 <= i and i < n }
}
