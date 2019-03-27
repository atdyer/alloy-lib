open yale
open sumprod
open yaleRefinement
open matrixMVM

pred MVM [Y: Yale, x, b: Matrix] {
  Y.rows = b.rows
  Y.cols = x.rows
  x.cols = 1
  b.cols = 1
  all i: Int {
    0 <= i and i < Y.rows => {
      let s = Y.IA[i],            -- start index for row
          t = Y.IA[add[i, 1]],    -- end index for row
          r = b.values[i][0] {    -- SumProd for row
            (no s or no t or s = t) => r = Zero else {
              let j = Y.JA.subseq[s, sub[t, 1]],   -- JA[s, t)
                  v = Y.A.subseq[s, sub[t, 1]] {   -- A[s, t)
                dotProd[j, v, x, r]
              }
            }
          }
    }
  }
}

pred dotProd [cols: Int->Int, vals: Int->Value, x: Matrix, b: SumProd] {
  all c: cols[univ] {
    let i = cols.c | b.values[c] = vals[i] -> x.values[c][0]
  }
  all c: Int - cols[univ] {
    no b.values[c]
  }
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

pred ref [Y: Yale, x, M, Yb, Mb: Matrix] {
  repInv[Y]
    and alpha[Y, M]
    and MVM[Y, x, Yb]
    and MVM[M, x, Mb]
}

-- refinement
check {
  all Y: Yale, x, M, Yb, Mb: Matrix {
    ref[Y, x, M, Yb, Mb] => solutionsEqv[Yb, Mb]
  }
} for 4
