module ell

-- https://web.ma.utexas.edu/CNA/ITPACK/manuals/userv2d/node3.html

open matrix
open util/integer

sig ELL {
  rows, cols, maxnz: Int,
  vals: seq Value,
  cids: seq Int
}

pred repInv [e: ELL] {
  e.rows >= 0
  e.cols >= 0
  e.maxnz >= 0
  e.maxnz <= e.cols
  let sz = mul[e.rows, e.maxnz] |
    #e.cids = sz and #e.vals = sz
  all j: e.cids.elems |
    gte[j, -1] and lt[j, e.cols]
  all i: range[e.rows], j: range[e.cols] |
    let s = mul[i, e.maxnz],
        t = sub[add[s, e.maxnz], 1] |
      #e.cids.subseq[s, t].indsOf[j] <= 1
  all i: Int |
    e.cids[i] = -1 <=> e.vals[i] = Zero
}

pred init [e: ELL, nrows, ncols, mnz: Int] {
  nrows >= 0
  ncols >= 0
  mnz >= 0
  mnz <= ncols
  e.rows = nrows
  e.cols = ncols
  e.maxnz = mnz
  #e.vals = mul[nrows, mnz]
  #e.cids = mul[nrows, mnz]
  e.cids[Int] = -1 or no e.cids[Int]
}

fun rowcols [e: ELL, row: Int]: seq Int {
  let a = mul[row, e.maxnz],
      b = add[a, e.maxnz] |
    e.cids.subseq[a, sub[b, 1]]
}

fun rowvals [e: ELL, row: Int]: seq Value {
  let a = mul[row, e.maxnz],
      b = add[a, e.maxnz] |
    e.vals.subseq[a, sub[b, 1]]
}

fun getrow [e: ELL, row: Int]: Int->Value {
  let cols = rowcols[e, row],
      vals = rowvals[e, row] | ~cols.vals
}

fun get [e: ELL, i, j: Int]: Value {
  not inrange[e, i, j] => none else
  let a = i.mul[e.maxnz],
      b = a.add[e.maxnz].sub[1],
      cs = e.cids.subseq[a, b],
      vs = e.vals.subseq[a, b],
      k = cs.idxOf[j] {
    no k => Zero else vs[k]
  }
}

pred inrange [e: ELL, i, j: Int] {
  i in range[e.rows] and j in range[e.cols]
}
