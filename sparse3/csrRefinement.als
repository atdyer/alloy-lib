open csr

-- abstraction function
pred alpha [c: CSR, m: Matrix] {
  m.rows = c.rows
  m.cols = c.cols
  m.values = { i: range[c.rows], j: range[c.cols], v: Value |
                 let k = { k: range[c.IA[i], c.IA[add[i, 1]]] | c.JA[k] = j } |
                   one k => v = c.A[k] else v = Zero }
}

pred alpha2 [c: CSR, m: Matrix] {
  m.rows = c.rows
  m.cols = c.cols
  all i, j: Int |
    get[c, i, j] = m.values[i][j]
}

pred show {
  some c: CSR, m: Matrix |
    repInv[c] and c.rows = 1 and c.cols = 2
      and alpha[c, m] and not alpha2[c, m]
        -- and some m2: Matrix | alpha2[c, m2]
}

run show for 1 CSR, 1 Matrix, 3 Value, 4 Int

assert alphaSame {
  all c: CSR, m: Matrix |
    repInv[c] => (alpha[c, m] <=> alpha2[c, m])
}

check alphaSame for exactly 1 CSR, 1 Matrix, 3 Value, 4 Int

assert repValid {
  all c: CSR, m: Matrix |
    repInv[c] and alpha[c, m] => repInv[m]
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
