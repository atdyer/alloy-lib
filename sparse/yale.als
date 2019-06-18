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

pred repInv [y: Yale] {
  Zero not in y.A.elems
  all i: y.IA.rest.elems | gte[i, 0] and lte[i, mul[y.rows, y.cols]]  -- IA values <= rows*cols
  all j: y.JA.elems | gte[j, 0] and lt[j, y.cols]                     -- JA values < cols
  y.IA[0] = 0
  y.IA.last = #y.A                               -- last value of IA is length of A
  #y.IA > 1 => gt[y.IA.last, y.IA.butlast.last]  -- last value of IA not repeated
  #y.A = #y.JA
  lte[#y.A, mul[y.rows, y.cols]]                 -- max length of A = rows*cols
  lte[#y.IA, add[y.rows, 1]]                     -- max length of IA = rows+1
  all i: y.IA.inds |
    i > 0 => let a = y.IA[sub[i, 1]],
                 b = y.IA[i],
                 n = sub[b, a] {
      b >= a                                -- values of IA increasing
      n <= y.cols                           -- max number of values in row
      #y.JA.subseq[a, sub[b, 1]].elems = n  -- column indices unique per row
    }
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
  val != Zero
  y'.IA = y.IA
  y'.JA = y.JA
  let a = y.IA[row],                 -- IA[row]
      b = y.IA[add[row, 1]],         -- IA[row+1]
      j = y.JA.subseq[a, sub[b, 1]], -- JA[a, b)
      i = add[a, j.idxOf[col]] |     -- index of val in A
    y'.A = y.A.setAt[i, val]
}

pred NZtoZ [y, y': Yale, row, col: Int, val: Value] {
  get[y, row, col] != Zero
  val = Zero
  let ai = row,
      bi = add[row, 1],
      li = sub[#y.IA, 1],
      a = y.IA[ai],                   -- IA[row]
      b = y.IA[bi],                   -- IA[row+1]
      j = y.JA.subseq[a, sub[b, 1]],  -- JA[a, b)
      i = add[a, j.idxOf[col]] {      -- index of val in A
    y'.A = y.A.delete[i]
    y'.JA = y.JA.delete[i]
    bi = li => {                    -- b is the last value in IA
      let bn = sub[b, 1],           -- new value for b
          ia = y.IA.setAt[bi, bn],  -- new IA
          bf = ia.idxOf[bn] |       -- first index of b in new IA
        y'.IA = ia.subseq[0, bf]    -- remove trailing values of b
    } else {
      #y'.IA = #y.IA
      y'.IA.subseq[0, ai] = y.IA.subseq[0, ai]
      subEach[y.IA.subseq[bi, li], y'.IA.subseq[bi, li], 1]
    }
  }
}

pred ZtoNZ [y, y': Yale, row, col: Int, val: Value] {

  #y.A < #seq/Int   -- avoid maximum sequence length issues
  #y.IA < #seq/Int

  get[y, row, col] = Zero
  val != Zero
  let a = y.IA[row],           -- IA[row]
      b = y.IA[add[row, 1]] {  -- IA[row+1]
    some a => {                                   -- IA[row] exists
      y'.IA.subseq[0, row] = y.IA.subseq[0, row]
      some b => let bi = add[row, 1],             -- IA[row+1] exists
                    li = sub[#y.IA, 1] {
        y'.A = y.A.insert[b, val]
        y'.JA = y.JA.insert[b, col]
        addEach[y.IA.subseq[bi, li], y'.IA.subseq[bi, li], 1]
        #y'.IA = #y.IA
      }
      no b => {                                   -- IA[row+1] doesn't exist
        y'.A = y.A.add[val]
        y'.JA = y.JA.add[col]
        y'.IA = y.IA.add[add[a, 1]]
      }
    }
    no a => {                                     -- IA[row] doesn't exist
      y'.A = y.A.add[val]
      y'.JA = y.JA.add[col]
      let l = #y.IA,         -- length of IA
          an = y.IA.last,    -- new value of a
          bn = add[an, 1] {  -- new value of b
        #y'.IA = add[row, 2]
        y'.IA.subseq[0, sub[l, 1]] = y.IA
        y'.IA.subseq[sub[l, 1], row].elems = an
        y'.IA.last = bn
      }
    }
  }
}

pred ZtoZ [y, y': Yale, row, col: Int, val: Value] {
  get[y, row, col] = Zero
  val = Zero
  y'.A = y.A
  y'.IA = y.IA
  y'.JA = y.JA
}

pred rowInRange [y: Yale, row: Int] {
  0 <= row and row < y.rows
}

pred colInRange [y: Yale, col: Int] {
  0 <= col and col < y.cols
}

pred addEach [s, s': seq Int, n: Int] {
  s.inds = s'.inds
  all i: s.inds | s'[i] = add[s[i], n]
}

pred subEach [s, s': seq Int, n: Int] {
  s.inds = s'.inds
  all i: s.inds | s'[i] = sub[s[i], n]
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
