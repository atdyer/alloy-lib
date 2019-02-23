module yale2

open matrix
open util/integer

sig Yale {
  rows: Int,
  cols: Int,
  A: seq Value,
  IA: seq Int,
  JA: seq Int
} {
  rows >= 0
  cols >= 0
}

-----
----- Operations
-----

pred init_yale [y: Yale, nrows, ncols: Int] {

  y.rows = nrows
  y.cols = ncols
  no y.A
  no y.JA
  y.IA = {0->0}

}

pred update_yale[y, y': Yale, row, col: Int, val: Value] {
  
  NZtoNZ[y, y', row, col, val] or
  NZtoZ[y, y', row, col, val] or
  ZtoNZ[y, y', row, col, val] or
  ZtoZ[y, y', row, col, val]

}

pred NZtoNZ [y, y': Yale, row, col: Int, val: Value] {

  -- same size
  y'.rows = y.rows
  y'.cols = y.cols

  -- row and col in range
  rowInRange[y, row]
  colInRange[y, col]

  -- current value is nonzero
  get[y, row, col] != Zero

  -- val is nonzero
  val != Zero

  -- all indices remain unchanged
  y'.IA = y.IA
  y'.JA = y.JA

  -- a = IA[row]
  -- b = IA[row+1]
  -- j = J[a, b)
  -- i = index of col in j
  let a = y.IA[row],
      b = y.IA[add[row, 1]],
      j = y.JA.subseq[a, sub[b, 1]],
      i = add[a, j.idxOf[col]] {

    y'.A = y.A.setAt[i, val]

  }

}

pred NZtoZ [y, y': Yale, row, col: Int, val: Value] {

  -- same size
  y'.rows = y.rows
  y'.cols = y.cols

  -- row and col in range
  rowInRange[y, row]
  colInRange[y, col]

  -- current value is nonzero
  get[y, row, col] != Zero

  -- val is zero
  val = Zero

  -- ai = index of a
  -- bi = index of b
  -- li = index of last value in IA
  -- a = IA[row]
  -- b = IA[row+1]
  -- c = index in JA[a, b] that contains col
  -- i = index of val in A and index in JA of col
  let ai = row,
      bi = add[row, 1],
      li = sub[#y.IA, 1],
      a = y.IA[ai],
      b = y.IA[bi],
      c = y.JA.subseq[a, sub[b, 1]].idxOf[col],
      i = add[a, c] {

    -- remove value from A
    y'.A = y.A.delete[i]

    -- remove column index from JA
    y'.JA = y.JA.delete[i]

    -- b is the last value in IA
    bi = li => {

      -- bn = new value of b
      -- ia = IA with the new value of b
      -- bf = the first index of the new value of b in ia
      let bn = sub[b, 1],
          ia = y.IA.setAt[bi, bn],
          bf = ia.idxOf[bn] {

        -- remove values of b except one
        y'.IA = ia.subseq[0, bf]

      }

    } 

    -- b is not the last value in IA
    else {

      -- length of IA does not change
      #y'.IA = #y.IA

      -- all IA[0, a] remain the same
      y'.IA.subseq[0, ai] = y.IA.subseq[0, ai]

      -- subtract one from all values in IA[bi, li]
      subEach[y.IA.subseq[bi, li], y'.IA.subseq[bi, li], 1]

    }

  }

}

pred ZtoNZ [y, y': Yale, row, col: Int, val: Value] {

  -- same size
  y'.rows = y.rows
  y'.cols = y.cols

  -- row and col in range
  rowInRange[y, row]
  colInRange[y, col]

  -- current value is zero
  get[y, row, col] = Zero

  -- val is nonzero
  val != Zero

  -- a = IA[row]
  -- b = IA[row+1]
  let a = y.IA[row],
      b = y.IA[add[row, 1]] {

    -- if IA contains a value for the start index of row,
    some a => {

      -- all IA values up to and include index row are unchanged
      y'.IA.subseq[0, row] = y.IA.subseq[0, row]

      -- if IA contains a value for the end index of row,
      -- we insert values into A and JA and add one to
      -- all values including and after the end index of
      -- the row in IA
      some b => 

        -- bi = index of b
        -- li = index of last value in IA
        let bi = add[row, 1],
            li = sub[#y.IA, 1] {

        y'.A = y.A.insert[b, val]
        y'.JA = y.JA.insert[b, col]
        addEach[y.IA.subseq[bi, li], y'.IA.subseq[bi, li], 1]

      }

      -- if IA doesn't contain a value for the end index of row,
      -- all values are simply appended
      no b => {

        y'.A = y.A.add[val]
        y'.JA = y.JA.add[col]
        y'.IA = y.IA.add[add[a, 1]]

      }

    }

    -- if IA does not have a value for the start index of row,
    -- we must extend IA until it ends with a and b and contains
    -- any intermediate values
    no a =>

      -- the value and column index are appended
      y'.A = y.A.add[val]
      y'.JA = y.JA.add[col]

      -- l = number of values in IA before adding val
      -- an = a-new = the value of a in the new IA
      -- bn = b-new = the value of b in the new IA
      let l = #y.IA,
          an = y.IA.last,
          bn = add[an, 1] {

        -- new IA begins with old IA
        y'.IA.subseq[0, sub[l, 1]] = y.IA

        -- new IA length is row + 2
        #y'.IA = add[row, 2]

        -- all new intermediate values are an
        -- s = last index of old IA
        -- t = next to last index of new IA
        let s = sub[#y.IA, 1],
            t = sub[#y'.IA, 2] {

          y'.IA.subseq[s, t].elems = an

        }

        -- new IA ends with bn
        y'.IA.last = bn

      }

  }

}

pred ZtoZ [y, y': Yale, row, col: Int, val: Value] {

  -- same size
  y'.rows = y.rows
  y'.cols = y.cols

  -- row and col in range
  rowInRange[y, row]
  colInRange[y, col]

  -- current value is zero
  get[y, row, col] = Zero

  -- val is zero
  val = Zero

  -- everything stays the same
  y'.A = y.A
  y'.IA = y.IA
  y'.JA = y.JA

}

-----
----- Representation Invariant
-----

pred repInv [y: Yale] {

  -- there are no zeros stored as values
  Zero not in y.A.elems

  -- all IA index values: 0 <= i <= rows * cols
  -- all JA index values: 0 <= j <  cols
  all i: y.IA.rest.elems | gte[i, 0] and lte[i, mul[y.rows, y.cols]]
  all j: y.JA.elems      | gte[j, 0] and lt[j, y.cols]

  -- the first value of IA must always be zero
  y.IA[0] = 0

  -- the last value of IA must be equal to the length of A
  y.IA.last = #y.A

  -- the last value of IA must not be repeated
  #y.IA > 1 => gt[y.IA.last, y.IA.butlast.last]

  -- A and JA must have the same length
  #y.A = #y.JA

  -- the maximum length of A is rows*cols
  lte[#y.A, mul[y.rows, y.cols]]

  -- the maximum length of IA is rows + 1
  lte[#y.IA, add[y.rows, 1]]

  all i: y.IA.inds |

    i > 0 =>
      let b = y.IA[i],
          a = y.IA[sub[i, 1]],
          n = sub[b, a] {

    -- all values of IA must be >= the previous value
    b >= a

    -- the difference between all pairs of values in IA must be <= cols
    n <= y.cols

    -- column indices must be unique for all row ranges
    #y.JA.subseq[a, sub[b, 1]].elems = n

  }

}

-----
----- Abstraction Function
-----

pred alpha [y: Yale, m: Matrix] {

  -- same number of rows and cols
  m.rows = y.rows
  m.cols = y.cols

  -- all values are the same
  all i, j: Int {
    rowInRange[y, i] and
    colInRange[y, j] =>
      m.values[i][j] = get[y, i, j]
  }

}

-----
----- Helper functions/predicates
-----

pred rowInRange [y: Yale, row: Int] {
  0 <= row and row < y.rows
}

pred colInRange [y: Yale, col: Int] {
  0 <= col and col < y.cols
}

-- s' is the sequence in which n is added to each value in sequence s
pred addEach [s, s': seq Int, n: Int] {

  s.inds = s'.inds

  all i: s.inds | s'[i] = add[s[i], n]

}

-- s' is the sequence in which n is subtracted from each value in sequence s
pred subEach [s, s': seq Int, n: Int] {

  s.inds = s'.inds

  all i: s.inds | s'[i] = sub[s[i], n]

}

fun get [y: Yale, row, col: Int]: Value {

  -- a = IA[row]
  -- b = IA[row+1]
  let a = y.IA[row], b = y.IA[add[row, 1]] {

    -- if a or b is empty, zero
    -- if a = b, zero
    (no a or no b or a = b) => Zero else {

      -- j = JA[a, b)
      -- v = A[a, b)
      -- i = index of col in j
      let j = y.JA.subseq[a, sub[b, 1]],
          v = y.A.subseq[a, sub[b, 1]],
          i = j.idxOf[col] {

        -- i is empty means zero, otherwise get value
        no i => Zero else v[i]

      }

    }

  }

}


-----
----- Assertions/Checks
-----

-- check that initial states do not violate the invariant
assert initValid {
  all y: Yale, i, j: Int | init_yale[y, i, j] => repInv[y]
}

check initValid for 5

-- check that nonzero -> nonzero update doesn't violate the invariant
assert NZtoNZvalid {
  all y, y': Yale, i, j: Int, v: Value |
    repInv[y] and NZtoNZ[y, y', i, j, v] => repInv[y']
}

check NZtoNZvalid for 5 but 0 Matrix

-- check that nonzero -> zero update doesn't violate the invariant
assert NZtoZvalid {
  all y, y': Yale, i, j: Int, v: Value |
    repInv[y] and NZtoZ[y, y', i, j, v] => repInv[y']
}

check NZtoZvalid for 5 but 0 Matrix, 2 Yale

-- check that zero -> nonzero update doesn't violate the invariant
assert ZtoNZvalid {
  all y, y': Yale, i, j: Int, v: Value |
    repInv[y] and ZtoNZ[y, y', i, j, v] => repInv[y']
}

check ZtoNZvalid for 5 but 0 Matrix

-- check that zero -> zero update doesn't violate the invariant
assert ZtoZvalid {
  all y, y': Yale, i, j: Int, v: Value |
    repInv[y] and ZtoZ[y, y', i, j, v] => repInv[y']
}

check ZtoZvalid for 5 but 0 Matrix

-- check that updates do not violate the invariant
assert updateValid {
  all y, y': Yale, i, j: Int, v: Value |
    repInv[y] and update_yale[y, y', i, j, v] => repInv[y']
}

check updateValid for 5 but 0 Matrix

-- check for refinement
assert refines {

  all y, y': Yale, m, m': Matrix, i, j: Int, v: Value {

    init_yale[y, i, j] and alpha[y, m] => init[m, i, j]

    repInv[y]
    and update_yale[y, y', i, j, v]
    and alpha[y, m]
    and alpha[y', m'] =>
      update[m, m', i, j, v]

  }

}

-- no counterexample found (~15min runtime)
check refines for 7


-----
----- Sample cases
-----

one sig One extends Value {}

pred testAddNZ {
  some y, y': Yale {
    y.rows = 4 and y'.rows = 4
    y.cols = 4 and y'.cols = 4
    #y.A = 1
    #y.IA = 3
    #y.JA = 1
    y.A[0] = One
    y.IA[0] = 0
    y.IA[1] = 0
    y.IA[2] = 1
    y.JA[0] = 1
    ZtoNZ[y, y', 3, 3, One]
  }
}

pred testRemoveNZ {
  some y, y': Yale {
    y.rows = 4 and y'.rows = 4
    y.cols = 4 and y'.cols = 4
    #y.A = 2
    #y.IA = 5
    #y.JA = 2
    y.A[0] = One
    y.A[1] = One
    y.IA[0] = 0
    y.IA[1] = 0
    y.IA[2] = 1
    y.IA[3] = 1
    y.IA[4] = 2
    y.JA[0] = 1
    y.JA[1] = 3
    NZtoZ[y, y', 3, 3, Zero]
  }
}

pred testRemoveNZR {
  some y, y': Yale {
    y.rows = 2 and y'.rows = 2
    y.cols = 2 and y'.cols = 2
    #y.A = 2
    #y.IA = 2
    #y.JA = 2
    y.A[0] = One
    y.A[1] = One
    y.IA[0] = 0
    y.IA[1] = 2
    y.JA[0] = 1
    y.JA[1] = 0
    NZtoZ[y, y', 0, 0, Zero]
  }
}

run testAddNZ for 8 but 0 Matrix, exactly 2 Yale
run testRemoveNZ for 8 but 0 Matrix, exactly 2 Yale
run testRemoveNZR for 5 but 0 Matrix, exactly 2 Yale
