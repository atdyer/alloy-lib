open csr

pred alpha [c: CSR, m: Matrix] {
  m.rows = c.rows
  m.cols = c.cols
  all i, j: Int |
    get[c, i, j] = m.values[i][j]
}

assert repValid {
  all c: CSR, m: Matrix |
    repInv[c] and alpha[c, m] => repInv[m]
}

assert refines {
  all c: CSR, m: Matrix, i, j: Int |
    init[c, i, j] and alpha[c, m] => init[m, i, j]
}

check repValid for 10 but exactly 1 CSR, exactly 1 Matrix
check refines for 10 but exactly 1 CSR, exactly 1 Matrix
