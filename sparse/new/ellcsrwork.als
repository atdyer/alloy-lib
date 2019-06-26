/*
http://people.sc.fsu.edu/~jburkardt%20/f_src/sparsekit/sparsekit.f90
Ctrl-F: ellcsr
*/

open ell
open ellRefinement
open csr
open csrRefinement
open util/integer

/**
Two methods for modeling ELL->CSR translation:
1. Loop through flattened iterations and use div/rem to
   determine place inside of loops.
2. Loop through variables and use loop indices to determine
   location inside of flattened iterations.
*/

pred genkpos [e: ELL, kpos: seq Int] {
  kpos[0] = 0
  #kpos = e.rows.mul[e.maxnz].add[1]        -- #kpos = rows*maxnz+1
  all i: rowInds[e] {                       -- i = current row
    all k: indices[e.maxnz] {               -- k = current index
      let it = i.mul[e.maxnz].add[k] {      -- it = i*maxnz+k
        rowcols[e, i][k] != -1 => {
          it < kpos.lastIdx => kpos[it.add[1]] = kpos[it].add[1]
        } else {
          it < kpos.lastIdx => kpos[it.add[1]] = kpos[it]
        }
      }
    }
  }
}

pred ellcsrnew [e: ELL, c: CSR] {
  e.rows = c.rows
  e.cols = c.cols
  c.IA[0] = 0
  #c.IA = c.rows.add[1]
  some kpos: seq Int {  -- using "one kpos" requires Alloy*, "some kpos" for Alloy
    genkpos[e, kpos]
    #c.A = kpos.last
    #c.JA = kpos.last
    all i: rowInds[e] {
      all k: indices[e.maxnz] {
        rowcols[e, i][k] != -1 =>
        let kp = kpos[i.mul[e.maxnz].add[k]] {
          c.A[kp] = rowvals[e, i][k]
          c.JA[kp] = rowcols[e, i][k]
        }
      }
      c.IA[i.add[1]] = kpos[i.add[1].mul[e.maxnz]]
    }
  }
}

pred isNonzero [e: ELL, i, k: Int] {
  rowcols[e, i][k] != -1
}

-- ell -> csr makes a valid csr
check {
  all e: ELL, c: CSR {
    -- e.rows > 0 and e.cols > 0 and -- e.maxnz > 0 and
    repInv[e] and ellcsrnew[e, c] => repInv[c]
  }
} for 7 seq, 0 Matrix, 1 ELL, 1 CSR, 2 Value

-- ell -> csr makes the same matrix
check {
  all e: ELL, c: CSR, m: Matrix {
    repInv[e] and alpha[e, m] and ellcsrnew[e, c] => alpha[c, m] and repInv[c]
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
    ellcsrnew[e, c]
  }
} for 7 seq, 1 ELL, 1 CSR, 2 Value, 0 Matrix








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
    -- when rows=0 or maxnz=0, IA is all 0s
    -- and A and JA are empty
    nsteps = 0 => {
      c.IA.elems = 0
      #c.A = 0
      #c.JA = 0
    }

  }
}

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


