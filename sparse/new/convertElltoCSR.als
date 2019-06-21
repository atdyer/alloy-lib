open ell
open ellRefinement
open csr
open csrRefinement

pred sameMatrix [e: ELL, c: CSR, m: Matrix] {
  repInv[e]
  repInv[c]
  alpha[e, m]
  alpha[c, m]
}

pred sameOrder [e: ELL, c: CSR] {
  let placeholders = e.C.indsOf[-1],
      cols = e.C.delete[placeholders],
      vals = e.V.delete[placeholders] {
    c.JA = cols
    c.A = vals
  }
}

pred differenceIsNumPlaceholders [e: ELL, c: CSR] {
  all row: rowInds[e] {
    let rc = rowcols[e, row],      -- E: columns indices for current row
        np = #rc.indsOf[-1],       -- E: num placeholders in current row
        si = c.IA[row],            -- Y: start index of row in IA
        ei = c.IA[add[row, 1]] {   -- Y: end index of row in IA
          sub[ei, si] = sub[e.maxnz, np]
    }
  }
}

assert ELLCSRIndexRelationship {
  all e: ELL, c: CSR, m: Matrix |
    sameMatrix[e, c, m] and sameOrder[e, c] =>
      differenceIsNumPlaceholders[e, c]
}

check ELLCSRIndexRelationship for 6 but exactly 1 ELL, exactly 1 CSR, exactly 1 Matrix

-----

pred leftAligned [e: ELL] {
  all row: rowInds[e] {
    let rc = rowcols[e, row],
        firstph = rc.idxOf[-1],
        lastidx = sub[e.maxnz, 1] {
      (firstph != none and firstph != lastidx) => 
        rc.subseq[firstph, lastidx].elems = -1
    }
  }
}

pred ELLCSRslicing [e: ELL, c: CSR] {
  all row: rowInds[e] {
    let rc = rowcols[e, row],
        firstph = rc.idxOf[-1] {
      c.IA[add[row, 1]] = add[c.IA[row], firstph]  -- IA[row+1] = IA[row] + firstph
      c.A.subseq[row, add[row, firstph]]  -- JA[row, row+firstph] = rc[0, firstph]
                                          -- A[row, row+firstph] = rv[0, firstph]
    }
  }
}

pred showLeftAligned {
  no CSR
  no Matrix
  one ELL
  some e: ELL | 
    repInv[e] and leftAligned[e] and e.rows > 1 and e.cols > 1 and e.maxnz > 1
    and some row: rowInds[e] | let rc = rowcols[e, row] | #rc.indsOf[-1] > 1
}

run showLeftAligned for 8

-----

pred showSame {
  some e: ELL, c: CSR, m: Matrix |
    sameMatrix[e, c, m] and sameOrder[e, c]
}

run showSame for 4 but exactly 1 ELL, exactly 1 CSR, exactly 1 Matrix

