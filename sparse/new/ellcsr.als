open ell
open ellRefinement
open csr
open csrRefinement
open util/integer

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

pred ellcsr [e: ELL, c: CSR] {
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

/* Checks:
 * 
 * Alloy checks performed using lingeling and Alloy* checks
 * using SAT4J. Time required for each check indicated next to
 * command, with the Alloy* time marked with a *.
 */

-- Check that the translation generates a valid CSR for up to 6x6
assert preservesRep {
  all e: ELL, c: CSR |
    repInv[e] and ellcsr[e, c] => repInv[c]
} 
check preservesRep for 4 Int, 7 seq, 0 Matrix, 1 ELL, 1 CSR, 2 Value   -- 9s, 66s*
check preservesRep for 4 Int, 7 seq, 0 Matrix, 1 ELL, 1 CSR, 5 Value   -- 7s, 70s*

-- Check that the translation is valid for matrices up to 6x6
assert transValid {
  all e: ELL, c: CSR, m: Matrix {
    repInv[e] and alpha[e, m] and ellcsr[e, c] => alpha[c, m] and repInv[c]
  }
} 
check transValid for 4 Int, 7 seq, 1 Matrix, 1 ELL, 1 CSR, 2 Value  -- 17s, 89s*
check transValid for 4 Int, 7 seq, 1 Matrix, 1 ELL, 1 CSR, 5 Value  -- 23s, 134s*

-- Check that the translation can occur in-place
assert inPlace {
  all e: ELL, kpos: seq Int {
    genkpos[e, kpos] => {
      all i: rowInds[e] {
        all k: indices[e.maxnz] {
          let idx = i.mul[e.maxnz].add[k] |
            kpos[idx] <= idx
        }
      }
    }
  }
}
check inPlace for 5 Int, 15 seq, 0 Matrix, 1 ELL, 0 CSR, 2 Value

/* Runs:
 *
 */
run {
  some e: ELL, c: CSR |
    interesting[e] and ellcsr[e, c]
} for 4 Int, 7 seq, 0 Matrix, 1 ELL, 1 CSR, 2 Value

pred interesting [e: ELL] {
  e.rows > 1
  e.cols > 1
  e.maxnz > 1
  repInv[e]
}
