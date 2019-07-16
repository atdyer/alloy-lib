open csr

-- abstraction function
pred alpha [c: CSR, m: Matrix] {
  m.rows = c.rows
  m.cols = c.cols
  m.vals = {
    i: range[c.rows], j: range[c.cols], v: Value |
      let k = { k: range[c.IA[i], c.IA[add[i, 1]]] | c.JA[k] = j } |
        one k => v = c.A[k] else v = Zero
  }
}


assert repValid {
  all c: CSR, m: Matrix |
    repInv[c] and alpha[c, m] => repInv[m]
}

assert initValid {
  all c: CSR, m: Matrix, i, j: Int |
    init[c, i, j] and alpha[c, m] => init[m, i, j]
}

-- up to 6x6 matrix, up to 7 stored values (5sec, lingeling)
-- up to 14x14 matrix, up to 15 stored values (33min, lingeling)
check repValid for exactly 1 CSR, exactly 1 Matrix, 8 Value, 4 Int, 7 seq
check repValid for exactly 1 CSR, exactly 1 Matrix, 16 Value, 5 Int, 15 seq

-- up to 6x6 matrix (~0sec)
-- up to 14x14 matrix (~0sec)
check initValid for exactly 1 CSR, exactly 1 Matrix, 2 Value, 4 Int, 7 seq
check initValid for exactly 1 CSR, exactly 1 Matrix, 2 Value, 5 Int, 15 seq


pred showsize [n: Int] {
  some c: CSR, m: Matrix {
    c.rows = n
    c.cols = n
    repInv[c] and alpha[c, m]
  }
}

-- show 6x6
run { showsize[6] } for exactly 1 CSR, exactly 1 Matrix, 8 Value, 4 Int, 7 seq
