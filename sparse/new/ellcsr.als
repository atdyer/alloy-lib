/*
http://people.sc.fsu.edu/~jburkardt%20/f_src/sparsekit/sparsekit.f90
Ctrl-F: ellcsr
*/

open ell
open ellRefinement
open csr
open csrRefinement

pred ellcsr [e: ELL, c: CSR] {
  e.rows = c.rows
  e.cols = c.cols
  c.IA[0] = 0
  #c.IA = add[c.rows, 1]
  let nsteps = mul[e.rows, e.maxnz] {

    some kpos: seq Int {
      #kpos = add[nsteps, 1]
      kpos[0] = 0  -- kpos before looping begins
      all ki: indices[nsteps] {  -- kpos index of the current step
        let i = div[ki, e.maxnz],
            k = rem[ki, e.maxnz] {
          isNonzero[e, i, k] => {
            c.A[kpos[ki]] = rowvals[e, i][k]
            c.JA[kpos[ki]] = rowcols[e, i][k]
            -- set kpos for the next step (if there is one)
            ki < kpos.lastIdx => kpos[add[ki, 1]] = add[kpos[ki], 1]
          } else {
            -- set kpos for the next step (if there is one)
            ki < kpos.lastIdx => kpos[add[ki, 1]] = kpos[ki]
          }
          -- the last k iteration just happened, so
          -- IA[i+1] = kpos
          k = sub[e.maxnz, 1] => c.IA[add[i, 1]] = kpos[add[ki, 1]]

          -- the last iteration of the algorithm just happened,
          -- so we now know the length of A and JA
          (i = sub[e.rows, 1] and k = sub[e.maxnz, 1]) =>
            (#c.A = kpos[add[ki, 1]] and
             #c.JA = kpos[add[ki, 1]])
        }
      }
    }

  }
}

pred isNonzero [e: ELL, i, k: Int] {
  rowcols[e, i][k] != -1
}

-- ell -> csr makes a valid csr
check {
  all e: ELL, c: CSR {
    e.rows > 0 and e.cols > 0 and e.maxnz > 0 and
    repInv[e] and ellcsr[e, c] => repInv[c]
  }
} for 7 seq, 0 Matrix, 1 ELL, 1 CSR, 3 Value

-- ell -> csr makes the same matrix
check {
  all e: ELL, c: CSR, m: Matrix {
    e.rows > 0 and e.cols > 0 and e.maxnz > 0 and
    repInv[e] and alpha[e, m] and
    ellcsr[e, c] => alpha[c, m]
  }
} for 7 seq, 1 Matrix, 1 ELL, 1 CSR, 2 Value

/*
/- - -\
|0 1 0|
|2 0 3|
|0 4 0|
\- - -/
*/
run {
  some e: ELL, c: CSR {
    e.rows = 3
    e.cols = 3
    e.maxnz = 2
    e.columns = { 0->1 + 1->-1 + 2->0 + 3->2 + 4->-1 + 5->1 }
    e.values[0] != Zero
    e.values[1] = Zero
    e.values[2] != Zero
    e.values[3] != Zero
    e.values[4] = Zero
    e.values[5] != Zero
    repInv[e]
    ellcsr[e, c]
  }
} for 7 seq, 1 ELL, 1 CSR, 2 Value, 0 Matrix


-- Failed first attempt.
/*
pred ellcsr [e: ELL, c: CSR] {
  c.rows = e.rows
  c.cols = e.cols
  some kpos: seq Int {
    kpos[0] = 0
    c.IA[0] = 0
    all i: rowInds[e] {
      c.IA[add[i, 1]] = kpos[mul[add[i, 1], e.maxnz]]
      all k: indices[e.maxnz] {
        let ki = kposindex[e, i, k],
            kn = add[ki, 1] {
          isNonzero[e, i, k] => {
            c.A[kpos[ki]] = rowvals[e, i][k]
            c.JA[kpos[ki]] = rowcols[e, i][k]
            kn < sz[e] => kpos[kn] = add[kpos[ki], 1]  -- kpos += 1
          } else {
            kn < sz[e] => kpos[add[ki, 1]] = kpos[ki]  -- kpos unchanged
          }
        }
      }
    }
  }
}

fun kposindex [e: ELL, i, k: Int]: Int {
  add[mul[i, e.maxnz], k]
}

fun sz [e: ELL]: Int {
  mul[e.rows, e.maxnz]
}

*/



