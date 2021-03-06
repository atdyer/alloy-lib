open csr

-- abstraction function
pred alpha [c: CSR, m: Matrix] {
  m.rows = c.rows
  m.cols = c.cols
  all i, j: Int |
    get[c, i, j] = m.values[i][j]
}

pred alphanew [c: CSR, m: Matrix] {
  m.rows = c.rows
  m.cols = c.cols
  m.values = { 
    i: rowInds[c], j: colInds[c], v: Value |
      (some k: Int | c.IA[i] <= k and k < c.IA[add[i, 1]]
                     and j = c.JA[k] and v = c.A[k])
      or v = Zero 
  }
}

assert repValid {
  all c: CSR, m: Matrix |
    repInv[c] and alphanew[c, m] => repInv[m]
}
-- up to 6x6 matrix, up to 7 stored values (4sec, lingeling)
-- up to 14x14 matrix, up to 15 stored values (16min, lingeling)
check repValid for exactly 1 CSR, exactly 1 Matrix, 8 Value, 4 Int, 7 seq
check repValid for exactly 1 CSR, exactly 1 Matrix, 16 Value, 5 Int, 15 seq

assert initValid {
  all c: CSR, m: Matrix, i, j: Int |
    init[c, i, j] and alpha[c, m] => init[m, i, j]
}

-- up to 6x6 matrix
-- up to 14x14 matrix
check initValid for exactly 1 CSR, exactly 1 Matrix, 2 Value, 4 Int, 7 seq
check initValid for exactly 1 CSR, exactly 1 Matrix, 2 Value, 5 Int, 15 seq

-- generate an nxn CSR and equivalent matrix
pred showsize [n: Int] {
  some c: CSR, m: Matrix {
    c.rows = n
    c.cols = n
    repInv[c] and alpha[c, m]
  }
}

run { showsize[6] } for exactly 1 CSR, exactly 1 Matrix, 8 Value, 4 Int, 7 seq
