module matrix

open value
open util/integer

sig Matrix {

  rows, cols: Int,
  values: Int -> Int -> Value

} {
  rows >= 0
  cols >= 0
  all i, j: Int |               -- all index values fall within bounds
    i->j in values.univ =>
      0 <= i and i < rows and
      0 <= j and j < cols
  let nvals = mul[rows, cols] |
    #values = nvals and         -- number of values in matrix is rows*cols
    #values.univ = nvals        -- every i, j index pair appears in matrix
}

pred init [m: Matrix, nrows, ncols: Int] {
  m.rows = nrows
  m.cols = ncols
  let valset = m.values[univ][univ] |  -- all values in matrix are zero,
    valset = Zero or no valset         -- allowing for a 0x0 matrix
}

pred update [m, m': Matrix, row, col: Int, val: Value] {
  m.rows = m'.rows
  m.cols = m'.cols
  rowInRange[m, row]
  colInRange[m, col]
  let curr = m.values[row][col] |
    m'.values = m.values - row->col->curr + row->col->val
}

pred rowInRange [m: Matrix, row: Int] {
  0 <= row and row < m.rows
}

pred colInRange [m: Matrix, col: Int] {
  0 <= col and col < m.cols
}
