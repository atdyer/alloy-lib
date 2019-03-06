open yale

pred repInv [y: Yale] {
  Zero not in y.A.elems
  all i: y.IA.rest.elems | gte[i, 0] and lte[i, mul[y.rows, y.cols]]  -- IA values <= rows*cols
  all j: y.JA.elems | gte[j, 0] and lt[j, y.cols]                     -- JA values < cols
  y.IA[0] = 0
  y.IA.last = #y.A                               -- last value of IA is length of A
  #y.IA > 1 => gt[y.IA.last, y.IA.butlast.last]  -- last value of IA not repeated
  #y.A = #y.JA
  lte[#y.A, mul[y.rows, y.cols]]                 -- max length of A = rows*cols
  lte[#y.IA, add[y.rows, 1]]                     -- max length of IA = rows+1
  all i: y.IA.inds |
    i > 0 => let a = y.IA[sub[i, 1]],
                 b = y.IA[i],
                 n = sub[b, a] {
      b >= a                                -- values of IA increasing
      n <= y.cols                           -- max number of values in row
      #y.JA.subseq[a, sub[b, 1]].elems = n  -- column indices unique per row
    }
}

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
check ZtoNZvalid for 2 but 0 Matrix, 7 seq
check ZtoZvalid for 2 but 0 Matrix
check updateValid for 2 but 0 Matrix, 7 seq
check refines for 2 but 7 seq
