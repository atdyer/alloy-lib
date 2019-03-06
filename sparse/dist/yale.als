module yale

open matrix
open util/integer

sig Yale {
  rows, cols: Int,
  A: seq Value,
  IA, JA: seq Int
} {
  rows >= 0
  cols >= 0
}

pred initYale [y: Yale, nrows, ncols: Int] {
  y.rows = nrows
  y.cols = ncols
  no y.A
  no y.JA
  y.IA = {0->0}
}

pred updateYale [y, y': Yale, row, col: Int, val: Value] {
  y'.rows = y.rows
  y'.cols = y.cols
  rowInRange[y, row]
  colInRange[y, col]
  NZtoNZ[y, y', row, col, val] or  -- nonzero to nonzero
  NZtoZ[y, y', row, col, val] or   -- nonzero to zero
  ZtoNZ[y, y', row, col, val] or   -- zero to nonzero
  ZtoZ[y, y', row, col, val]       -- zero to zero
}

pred NZtoNZ [y, y': Yale, row, col: Int, val: Value] {
  get[y, row, col] != Zero
  y'.IA = y.IA
  y'.JA = y.JA
  let a = y.IA[row],                 -- IA[row]
      b = y.IA[add[row, 1]],         -- IA[row+1]
      j = y.JA.subseq[a, sub[b, 1]], -- JA[a, b)
      i = add[a, j.idxOf[col]] |     -- index of col in j
    y'.A = y.A.setAt[i, val]
}

pred ZtoZ [y, y': Yale, row, col: Int, val: Value] {
  get[y, row, col] = Zero
  val = Zero
  y'.A = y.A
  y'.IA = y.IA
  y'.JA = y.JA
}

pred rowInRange [y: Yale, row: Int] {
  0 <= row and col < y.cols
}

pred colInRange [y: Yale, col: Int] {
  0 <= col and col < y.cols
}

fun get [y: Yale, row, col: Int]: Value {
  let a = y.IA[row],            -- IA[row]
      b = y.IA[add[row, 1]] {   -- IA[row+1]
    (no a or no b or a = b) => Zero else {
      let j = y.JA.subseq[a, sub[b, 1]],  -- JA[a, b)
          v = y.A.subseq[a, sub[b, 1]],   -- A[a, b)
          i = j.idxOf[col] {              -- index of col in j
        no i => Zero else v[i]
      }
    }
  }
}
