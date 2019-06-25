module ell

-- https://web.ma.utexas.edu/CNA/ITPACK/manuals/userv2d/node3.html

open matrix
open util/integer

sig ELL {
  rows, cols, maxnz: Int,
  values: seq Value,
  columns: seq Int
} {
  rows >= 0
  cols >= 0
  maxnz >= 0
}

pred repInv [e: ELL] {
  e.rows >= 0
  e.cols >= 0
  e.maxnz >= 0
  e.maxnz <= e.cols
  let sz = mul[e.rows, e.maxnz] |
    #e.columns = sz and #e.values = sz
  all j: e.columns.elems |
    gte[j, -1] and lt[j, e.cols]
  all i: rowInds[e], j: colInds[e] |
    let s = mul[i, e.maxnz],
        t = sub[add[s, e.maxnz], 1] |
      #e.columns.subseq[s, t].indsOf[j] <= 1
  all i: Int |
    e.columns[i] = -1 <=> e.values[i] = Zero
}

-- initialize empty ELL
pred init [e: ELL, nrows, ncols, mnz: Int] {
  nrows >= 0
  ncols >= 0
  mnz >= 0
  mnz <= ncols
  e.rows = nrows
  e.cols = ncols
  e.maxnz = mnz
  #e.values = mul[nrows, mnz]
  #e.columns = mul[nrows, mnz]
  e.values[Int] = Zero or no e.values[Int]
  e.columns[Int] = -1 or no e.columns[Int]
}

-- create [0:e.rows)
fun rowInds [e: ELL]: Int {
  { i: Int | 0 <= i and i < e.rows }
}

-- create [0:e.cols)
fun colInds[e: ELL]: Int {
  { j: Int | 0 <= j and j < e.cols }
}

-- get seq of columns for a single row
fun rowcols [e: ELL, row: Int]: seq Int {
  let a = mul[row, e.maxnz],
      b = add[a, e.maxnz] {
    e.columns.subseq[a, sub[b, 1]]
  }
}

-- get seq of values for a single row
fun rowvals [e: ELL, row: Int]: seq Value {
  let a = mul[row, e.maxnz],
      b = add[a, e.maxnz] {
    e.values.subseq[a, sub[b, 1]]
  }
}

-- create {column->value} for a single row
fun getrow [e: ELL, row: Int]: Int->Value {
  let cols = rowcols[e, row],
      vals = rowvals[e, row] | ~cols.vals
}

-- retrieve a value from the matrix
fun get [e: ELL, row, col: Int]: Value {
  (row not in rowInds[e] or col not in colInds[e]) => none else
  let val = getrow[e, row][col] |
    no val => Zero else val
}
