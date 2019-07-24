module matrixTranspose

open matrix

pred transpose [m, m': Matrix] {
  m.rows = m'.cols
  m.cols = m'.rows
  m.vals.Value = ~(m'.vals.Value)
  all i: range[m.rows], j: range[m.cols] |
    m.vals[i][j] = m'.vals[j][i]
}

run {
  some m, m': Matrix | repInv[m] and transpose[m, m'] and m.rows = 2 and m.cols = 3
} for 4
