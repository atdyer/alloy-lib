open ell
open ellRefinement
open yale
open yaleRefinement

pred ellToYale [e: ELL, y: Yale] {
  all i: indices[e.rows] {                           -- i = 0:nrows
    all k: indices[e.maxnz] {                        -- k = 0:maxnz
      let kpos = add[mul[i, e.maxnz], k] {
        e.values[kpos] != Zero => {                  -- if values[i,k] != 0
          y.A[kpos] = e.values[kpos]
        }
      }
    }
  }
}

pred sameSize [e: ELL, y: Yale] {
  e.rows = y.rows
  e.cols = y.cols
}

fun indices [r: Int]: Int {
  { i: Int | 0 <= i and i < r }
}

assert ellToYaleValid {
  all e: ELL, y: Yale {
    repInv[e] and ellToYale[e, y] => repInv[y]
  }
}

check ellToYaleValid for 4


pred fullELL [e: ELL] {
  Zero not in e.values[Int]
  #e.values = mul[e.rows, e.maxnz]
  e.maxnz > 0
}

assert fullELLisYale {
  all e: ELL, y: Yale, m: Matrix {
    repInv[e] and
    repInv[y] and
    fullELL[e] and
    alpha[e, m] and
    e.values = y.A and    -- overspecify
    e.columns = y.JA and  -- overspecify
    alpha[y, m] => {
      all i: indices[sub[e.rows, 1]] {
        y.IA[add[i, 1]] = add[y.IA[i], e.maxnz]
      }
    }
  }
}

check fullELLisYale for 6 but exactly 1 ELL, exactly 1 Yale, 1 Matrix
