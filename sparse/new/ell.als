module ell

open matrix
open util/integer

sig ELL {
  rows, cols, maxnz: Int,
  V: seq Value,
  C: seq Int
}

pred repInv [e: ELL] {

  -- prevent overflows
  mul[e.rows, e.maxnz] >= e.rows
  mul[e.rows, e.maxnz] >= e.maxnz

  e.rows >= 0                   -- rows >= 0
  e.cols >= 0                   -- cols >= 0
  e.maxnz >= 0                  -- maxnz >= 0
  #e.C = mul[e.rows, e.maxnz]   -- length of C is rows*maxnz
  #e.V = mul[e.rows, e.maxnz]   -- length of V is rows*maxnz

  -- column indices >= -1
  all j: e.C.elems | gte[j, -1] and lt[j, e.cols]

  -- column indices are unique per row
  all i: rowInds[e], j: colInds[e] |
    let rc = rowcols[e, i] |
      #rc.indsOf[j] <= 1

  -- column index -1 always corresponds to Zero in values array
  all i: Int |
    e.C[i] = -1 <=> e.V[i] = Zero

}

pred init [e: ELL, nrows, ncols, nz: Int] {
  nrows >= 0
  ncols >= 0
  0 <= nz and nz <= ncols
  e.rows = nrows
  e.cols = ncols
  e.maxnz = nz
  #e.V = mul[e.rows, e.maxnz]
  #e.C = mul[e.rows, e.maxnz]
  e.V[Int] = Zero or no e.V[Int]
  e.C[Int] = -1 or no e.C[Int]
}


fun rowInds [e: ELL]: Int {
  { i: Int | 0 <= i and i < e.rows }
}

fun colInds [e: ELL]: Int {
  { i: Int | 0 <= i and i < e.cols }
}

fun rowcols [e: ELL, r: Int]: seq Int {
  let a = mul[r, e.maxnz],
      b = add[a, e.maxnz] {
    e.C.subseq[a, sub[b, 1]]
  }
}

fun rowvals [e: ELL, r: Int]: seq Value {
  let a = mul[r, e.maxnz],
      b = add[a, e.maxnz] {
    e.V.subseq[a, sub[b, 1]]
  }
}

fun get [e: ELL, row, col: Int]: Value {
  (row < 0 or row >= e.rows or
   col < 0 or col >= e.cols) => none else {
    let sc = rowcols[e, row],
        sv = rowvals[e, row],
        i = sc.idxOf[col] {
        no i => Zero else sv[i]
    }
  }
}
