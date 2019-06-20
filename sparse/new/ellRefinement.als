open ell

pred alpha [e: ELL, m: Matrix] {
  e.rows = m.rows
  e.cols = m.cols
  all i, j: Int |
    get[e, i, j] = m.values[i][j]
}

assert repValid {
  all e: ELL, m: Matrix |
    repInv[e] and alpha[e, m] => repInv[m]
}

assert refines {
  all e: ELL, m: Matrix, i, j, z: Int |
    init[e, i, j, z] and alpha[e, m] => init[m, i, j]
}

check repValid for 10 but exactly 1 ELL, exactly 1 Matrix
check refines for 10 but exactly 1 ELL, exactly 1 Matrix
