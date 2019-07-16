open ell
open util/integer

-- abstraction function
pred alpha [e: ELL, m: Matrix] {
  e.rows = m.rows
  e.cols = m.cols
  m.vals = {
    i: range[e.rows], j: range[e.cols], v: Value |
      let row = getrow[e, i] |
        no row[j] => v = Zero else v = row[j]
  }
}

assert repValid {
  all e: ELL, m: Matrix |
    repInv[e] and alpha[e, m] => repInv[m]
}

assert initValid {
  all e: ELL, m: Matrix, i, j, z: Int |
    init[e, i, j, z] and alpha[e, m] => init[m, i, j]
}

-- up to 7 rows, 7 values (~1 sec, lingeling)
-- up to 15 rows, 15 values (~30sec, lingeling)
check repValid for exactly 1 ELL, exactly 1 Matrix, 8 Value, 4 Int, 7 seq
check repValid for exactly 1 ELL, exactly 1 Matrix, 16 Value, 5 Int, 15 seq

-- up to 7 rows (~0sec)
-- up to 15 rows (~0sec)
check initValid for exactly 1 ELL, exactly 1 Matrix, 2 Value, 4 Int, 7 seq
check initValid for exactly 1 ELL, exactly 1 Matrix, 2 Value, 5 Int, 15 seq

run {
  some e: ELL, m: Matrix |
    repInv[e] and alpha[e, m] and Value in m.vals[univ][univ]
    and m.rows = 2 and m.cols = 2
} for exactly 1 ELL, exactly 1 Matrix, 2 Value, 4 Int, 7 seq



check {
  all e: ELL, m: Matrix |
    repInv[e] and alphaBuggy[e, m] => repInv[m]
}
check {
  all e: ELL, m: Matrix |
    repInv[e] and alpha[e, m] => repInv[m]
}
check {
  all e: ELL, m, mb: Matrix |
    repInv[e] and alpha[e, m] and alphaBuggy[e, mb] => m.vals = mb.vals
}

pred alphaBuggy [e: ELL, m: Matrix] {
  e.rows = m.rows
  e.cols = m.cols
  m.vals = {
    i: range[e.rows], j: range[e.cols], v: Value |
      let rc = rowcols[e, i], rv = rowvals[e, i] |
        (rc[j] = -1 or no rc[j]) => (v = Zero) else (v = rv[j])
  }
}
