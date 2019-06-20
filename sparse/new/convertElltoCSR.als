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

pred showSame {
  some e: ELL, c: CSR, m: Matrix |
    sameMatrix[e, c, m] and sameOrder[e, c]
}

run showSame for 4 but exactly 1 ELL, exactly 1 CSR, exactly 1 Matrix

