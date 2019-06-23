module matrix

open value
open util/integer

sig Matrix {
  rows, cols: Int,
  values: (Int -> Int) -> lone Value
}

pred repInv [m: Matrix] {
  m.rows >= 0
  m.cols >= 0
  m.values.univ = rowInds[m]->colInds[m]
}

pred init [m: Matrix, nrows, ncols: Int] {
  nrows >= 0
  ncols >= 0
  m.rows = nrows
  m.cols = ncols
  m.values = rowInds[m]->colInds[m]->Zero
}

fun indices [r: Int]: Int {
  { i: Int | 0 <= i and i < r }
}

fun rowInds [m: Matrix]: Int {
  { i: Int | 0 <= i and i < m.rows }
}

fun colInds [m: Matrix]: Int {
  { j: Int | 0 <= j and j < m.cols }
}
