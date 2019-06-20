module csr

open matrix
open util/integer

sig CSR {
  rows, cols: Int,
  A: seq Value,
  IA, JA: seq Int
}

pred repInv [c: CSR] {

  c.rows >= 0                      -- rows >= 0
  c.cols >= 0                      -- cols >= 0
  c.IA[0] = 0                      -- first value of IA is 0
  c.IA.last = #c.A                 -- last value of IA is lenth of A
  #c.IA = add[c.rows, 1]           -- length of IA is rows + 1
  #c.A = #c.JA                     -- A and JA same length
  lte[#c.A, mul[c.rows, c.cols]]   -- length of A <= rows * cols
  Zero not in c.A.elems            -- no zeros stored

  -- values of IA increasing
  all i: indices[c.rows] |
    c.IA[i] <= c.IA[add[i, 1]]

  -- values of JA <= cols
  all j: c.JA.elems | lte[0, j] and lt[j, c.cols]

}

pred init [c: CSR, nrows, ncols: Int] {
  nrows >= 0
  ncols >= 0
  c.rows = nrows
  c.cols = ncols
  no c.A
  no c.JA
  c.IA[Int] = 0
  #c.IA = add[nrows, 1]
}

fun rowInds [c: CSR]: Int {
  { i: Int | 0 <= i and i < c.rows }
}

fun colInds [c: CSR]: Int {
  { i: Int | 0 <= i and i < c.cols }
}

fun get [c: CSR, row, col: Int]: Value {
  let a = c.IA[row],
      b = c.IA[add[row, 1]] {
    (no a or no b) => none else {
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
