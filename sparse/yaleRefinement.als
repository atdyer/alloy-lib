open yale

pred alpha [y: Yale, m: Matrix] {
  m.rows = y.rows
  m.cols = y.cols
  all i, j: Int |
    rowInRange[y, i] and
    colInRange[y, j] => 
      m.values[i][j] = get[y, i, j]
}

pred validIndices [y, y': Yale, i, j: Int] {
  y'.rows = y.rows
  y'.cols = y.cols
  rowInRange[y, i]
  colInRange[y, j]
}

assert initValid {
  all y: Yale, i, j: Int |
    initYale[y, i, j] => repInv[y]
}

assert NZtoNZvalid {
  all y, y': Yale, i, j: Int, v: Value |
    validIndices[y, y', i, j] and
    repInv[y] and NZtoNZ[y, y', i, j, v] => repInv[y']
}

assert NZtoZvalid {
  all y, y': Yale, i, j: Int, v: Value |
    validIndices[y, y', i, j] and
    repInv[y] and NZtoZ[y, y', i, j, v] => repInv[y']
}

assert ZtoNZvalid {
  all y, y': Yale, i, j: Int, v: Value |
    validIndices[y, y', i, j] and
    repInv[y] and ZtoNZ[y, y', i, j, v] => repInv[y']
}

assert ZtoZvalid {
  all y, y': Yale, i, j: Int, v: Value |
    validIndices[y, y', i, j] and
    repInv[y] and ZtoZ[y, y', i, j, v] => repInv[y']
}

assert updateValid {
  all y, y': Yale, i, j: Int, v: Value |
    repInv[y] and updateYale[y, y', i, j, v] => repInv[y']
}

assert refines {
  all y, y': Yale, m, m': Matrix, i, j: Int, v: Value {
    initYale[y, i, j] and alpha[y, m] => init[m, i, j]
    repInv[y]
    and updateYale[y, y', i, j, v]
    and alpha[y, m]
    and alpha[y', m'] =>
      update[m, m', i, j, v]
  }
}

check initValid for 2 but 0 Matrix
check NZtoNZvalid for 2 but 0 Matrix
check NZtoZvalid for 2 but 0 Matrix
check ZtoNZvalid for 2 but 0 Matrix
check ZtoZvalid for 2 but 0 Matrix
check updateValid for 2 but 0 Matrix
check refines for 2
