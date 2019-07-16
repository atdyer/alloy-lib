module matrix

open value
open util/integer

sig Matrix {
  rows, cols: Int,
  vals: (Int -> Int) -> lone Value
}

pred repInv [m: Matrix] {
  m.rows >= 0
  m.cols >= 0
  m.vals.univ = range[m.rows]->range[m.cols]
}

pred init [m: Matrix, nrows, ncols: Int] {
  nrows >= 0
  ncols >= 0
  m.rows = nrows
  m.cols = ncols
  m.vals = range[m.rows]->range[m.cols]->Zero
}

fun range [n: Int]: set Int {
  { i: Int | 0 <= i and i < n }
}

fun range [m, n: Int]: set Int {
  { i: Int | m <= i and i < n }
}
