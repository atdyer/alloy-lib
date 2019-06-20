open ell
open ellRefinement
open yale
open yaleRefinement

pred sameMatrix [e: ELL, y: Yale, m: Matrix] {
  repInv[e]
  repInv[y]
  alpha[e, m]
  alpha[y, m]
}

pred sameOrder [e: ELL, y: Yale] {
  let placeholders = e.columns.indsOf[-1],
      c = e.columns.delete[placeholders],
      v = e.values.delete[placeholders] {
    y.JA = c
    y.A = v
  }
}

pred show {
   some e: ELL, y: Yale, m: Matrix |
     sameMatrix[e, y, m] and sameOrder[e, y]
}

run show for 4 but exactly 1 ELL, exactly 1 Yale, exactly 1 Matrix

fun rowInds [e: ELL]: Int {
  { i: Int | 0 <= i and i < e.rows }
}

pred differenceIsNumPlaceholders [e: ELL, y: Yale] {
  all row: rowInds[e] {
    let rc = rowcols[e, row],     -- E: column indices for current row
        np = #rc.indsOf[-1],      -- E: num placeholders in current row
        si = y.IA[row],           -- Y: start index of row in IA
        ei = y.IA[add[row, 1]] {  -- Y: end index of row in IA
      sub[ei, si] = sub[e.maxnz, np]
    }
  }
}

assert yaleEllIndexRelationship {
  all e: ELL, y: Yale, m: Matrix {
    sameMatrix[e, y, m] and sameOrder[e, y] and e.maxnz > 1 => 
      differenceIsNumPlaceholders[e, y]
  }
}

check yaleEllIndexRelationship for 6 but exactly 1 ELL, exactly 1 Yale, exactly 1 Matrix
