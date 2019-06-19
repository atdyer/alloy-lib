open ell
open sumprod
open ellRefinement
open matrixMVM

pred MVM [e: ELL, x, b: Matrix] {
  e.rows = b.rows
  e.cols = x.rows
  x.cols = 1
  b.cols = 1
  all row: Int {
    0 <= row and row < e.rows => {
      let sc = rowcols[e, row],    -- subarray of cols
          sv = rowvals[e, row],    -- subarray of vals
          res = b.values[row][0] { -- resulting sumprod
        dotProd[sc, sv, x, res]
      }
    }
  }
}

pred dotProd [cols: Int->Int, vals: Int->Value, x: Matrix, b: SumProd] {
  all c: cols[univ] {
    let i = cols.c | 
      i != -1 => b.values[c] = vals[i] -> x.values[c][0]
  }
  all c: Int - cols[univ] {
    no b.values[c]
  }
  no b.values[-1]
}

pred solutionsEqv [a, b: Matrix] {
  a.rows = b.rows
  a.cols = b.cols
  all i, j: Int {
    0 <= i and i < a.rows and
    0 <= j and j < a.cols => {
      i->j in b.values.univ
      let aval = a.values[i][j],
          bval = b.values[i][j] {
        valEqv[aval, bval]
      }
    }
  }
}

pred ref [E: ELL, x, M, Eb, Mb: Matrix] {
  repInv[E]
    and alpha[E, M]
    and MVM[E, x, Eb]
    and MVM[M, x, Mb]
}

-- (sat4j) No counterexample found. Assertion may be valid. 54026ms.
-- (lingeling) No counterexample found. Assertion may be valid. 10117ms.
check {
  all E: ELL, x, M, Eb, Mb: Matrix {
    ref[E, x, M, Eb, Mb] => solutionsEqv[Eb, Mb]
  }
} for 4
