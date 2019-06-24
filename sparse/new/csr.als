module csr

open matrix
open util/integer

sig CSR {
  rows, cols: Int,
  A: seq Value,
  IA, JA: seq Int
}

pred repInv [c: CSR] {

  c.rows >= 0              -- rows >= 0
  c.cols >= 0              -- cols >= 0
  c.IA[0] = 0              -- first value of IA is 0
  c.IA.last = #c.A         -- last value of IA is length of A
  #c.IA = add[c.rows, 1]   -- length of IA is rows + 1
  #c.A = #c.JA             -- A and JA same length
  Zero not in c.A.elems    -- no zeros stored

  -- values of IA increasing
  all i: indices[c.rows] |
    c.IA[i] <= c.IA[add[i, 1]]

  -- column indices less than number of columns
  all j: c.JA.elems | lte[0, j] and lt[j, c.cols]

  -- column indices unique per row
  all i: indices[c.rows] |
    let a = c.IA[i], b = c.IA[add[i, 1]] |
      !c.JA.subseq[a, sub[b, 1]].hasDups

}

pred init [c: CSR, nrows, ncols: Int] {
  nrows >= 0
  ncols >= 0
  c.rows = nrows
  c.cols = ncols
  no c.A
  no c.JA
  c.IA = rowInds[c]->0 + nrows->0
}

fun rowInds [c: CSR]: Int {
  { i: Int | 0 <= i and i < c.rows }
}

fun colInds [c: CSR]: Int {
  { i: Int | 0 <= i and i < c.cols }
}

fun rowcols [c: CSR, row: Int]: seq Int {
  let a = c.IA[row],
      b = c.IA[add[row, 1]] {
    (no a or no b) => {none->none} else {
      c.JA.subseq[a, sub[b, 1]]
    }
  }
}

fun rowvals [c: CSR, row: Int]: seq Value {
  let a = c.IA[row],
      b = c.IA[add[row, 1]] {
    (no a or no b) => {none->none} else {
      c.A.subseq[a, sub[b, 1]]
    }
  }
}

fun getrow [c: CSR, row: Int]: Int->Value {
  let cols = rowcols[c, row],
      vals = rowvals[c, row] | ~cols.vals
}

fun get [c: CSR, row, col: Int]: Value {
  let a = c.IA[row],
      b = c.IA[add[row, 1]] {
    (no a or no b or col not in colInds[c]) => none else {
      a = b => Zero else {
        let j = c.JA.subseq[a, sub[b, 1]],
            v = c.A.subseq[a, sub[b, 1]],
            i = j.idxOf[col] {
          no i => Zero else v[i]
        }
      }
    }
  }
}
