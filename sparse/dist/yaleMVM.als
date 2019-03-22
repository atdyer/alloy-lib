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
  #cols = #vals
  #cols = #b.values
  all i: Int {
    0 <= i and i < #cols => {
      let col = cols[i],
          val = vals[i] {
            b.values[col] = val -> x.values[col][0]
          }
    }
  }
}

pred showSPMV {
  some Y: Yale, x, b: Matrix | 
    repInv[Y]
    and MVM[Y, x, b]
}

run showSPMV for 5

assert mvmRefines {
  all Y: Yale, x, M, Yb, Mb: Matrix {
    repInv[Y] and alpha[Y, M]
  }
}
