open matrix

pred ZtoNZ[m, m': Matrix, i, j: Int, v: Value] {
  m.vals[i][j] = Zero
  v != Zero
  m'.rows = m.rows
  m'.cols = m.cols
  let u = m.vals[i][j] |
    m'.vals = m.vals - i->j->u + i->j->v
}

-- preserve abstract rep invariant
check {
  all m, m': Matrix, i, j: Int, v: Value |
    repInv[m] and ZtoNZ[m, m', i, j, v] => repInv[m']
} for 2 Matrix, 5 Value
