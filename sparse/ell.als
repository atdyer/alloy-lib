module ell

open matrix
open util/integer

sig ELL {
  rows, cols: Int,
  maxnz: Int,
  values: seq Value,
  columns: seq Int
}

pred repInv [e: ELL] {

  lte[e.maxnz, e.cols]

  -- size of both arrays in nrows * maxnz
  #e.columns = mul[e.rows, e.maxnz]
  #e.values = mul[e.rows, e.maxnz]

  -- column indices >= 0 except placeholder (-1)
  -- column indices less than cols
  all i: e.columns.elems | gte[i, -1] and lt[i, e.cols]

  -- column indices are unique per row
  all i, j: Int |
    rowInRange[e, i] and
    colInRange[e, j] =>
      let rc = rowcols[e, i] | 
        #rc.indsOf[j] <= 1
}

---

pred initELL [e: ELL, nrows, ncols, nz: Int] {
  e.rows = nrows
  e.cols = ncols
  e.maxnz = nz
  #e.values = mul[e.rows, e.maxnz]
  #e.columns = mul[e.rows, e.maxnz]
  e.values[Int] = Zero
  e.columns[Int] = -1
}

pred NZtoNZ [e, e': ELL, row, col: Int, val: Value] {
  get[e, row, col] != Zero
  val != Zero
  e'.columns = e.columns
  let a = mul[row, e.maxnz],                 -- row start index
      b = add[a, e.maxnz],                   -- row end index
      sc = e.columns.subseq[a, sub[b, 1]],   -- row columns
      i = add[a, sc.idxOf[col]] {            -- index of col in e.columns
    e'.values = e.values.setAt[i, val]
  }
}

pred ZtoZ [e, e': ELL, row, col: Int, val: Value] {
  get[e, row, col] = Zero
  val = Zero
  e'.values = e.values
  e'.columns = e.columns
}

---

pred rowInRange [e: ELL, row: Int] {
  0 <= row and row < e.rows
}

pred colInRange [e: ELL, col: Int] {
  0 <= col and col < e.cols
}

fun get [e: ELL, r, c: Int]: Value {
  let sc = rowcols[e, r],
      sv = rowvals[e, r],
      i = sc.idxOf[c] {
    no i => Zero else sv[i]
  }
}

fun rowcols [e: ELL, r: Int]: seq Int {
  let a = mul[r, e.maxnz],
      b = add[a, e.maxnz] {
    e.columns.subseq[a, sub[b, 1]]
  }
}

fun rowvals [e: ELL, r: Int]: seq Value {
  let a = mul[r, e.maxnz],
      b = add[a, e.maxnz] {
    e.values.subseq[a, sub[b, 1]]
  }
}

---

pred show {
  all e: ELL | initELL[e, 2, 2, 2]
}

run show for 10 but exactly 1 ELL, 0 Matrix
