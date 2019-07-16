module matrix

open value
open util/integer

sig Matrix {
  rows, cols: Int,
  values: (Int -> Int) -> lone Value
}{
  rows >= 0 and cols >= 0
  rows = 0 <=> cols = 0
  values.univ = rowInds[this]->colInds[this]
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

fun range [n: Int]: set Int {
  { i: Int | 0 <= i and i < n }
}

fun range [m, n: Int]: set Int {
  { i: Int | m <= i and i < n }
}

-- create [0:r)
fun indices [r: Int]: Int {
  { i: Int | 0 <= i and i < r }
}

-- create [0:m.rows)
fun rowInds [m: Matrix]: Int {
  { i: Int | 0 <= i and i < m.rows }
}

-- create [0:m.cols)
fun colInds [m: Matrix]: Int {
  { j: Int | 0 <= j and j < m.cols }
}
