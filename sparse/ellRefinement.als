open ell

pred alpha [e: ELL, m: Matrix] {
  m.rows = e.rows
  m.cols = e.cols
  all i, j: Int |
    rowInRange[e, i] and
    colInRange[e, j] =>
      m.values[i][j] = get[e, i, j]
}

pred validIndices [e, e': ELL, i, j: Int] {
  e'.rows = e.rows
  e'.cols = e.cols
  e'.maxnz = e.maxnz
  rowInRange[e, i]
  rowInRange[e, j]
}

assert initValid {
  all e: ELL, i, j, k: Int |
    initELL[e, i, j, k] => repInv[e]
}

assert NZtoNZvalid {
  all e, e': ELL, i, j: Int, v: Value |
    validIndices[e, e', i, j] and
    repInv[e] and NZtoNZ[e, e', i, j, v] => repInv[e']
}

assert ZtoZvalid {
  all e, e': ELL, i, j: Int, v: Value |
    validIndices[e, e', i, j] and
    repInv[e] and ZtoZ[e, e', i, j, v] => repInv[e']
}

assert refines {
  all e: ELL, i, j, k: Int, m: Matrix {
    initELL[e, i, j, k] and alpha[e, m] => init[m, i, j]
  }
}

check initValid for 5 but 0 Matrix
check NZtoNZvalid for 5 but 0 Matrix, exactly 2 ELL
check ZtoZvalid for 2 but 0 Matrix
check refines for 5
