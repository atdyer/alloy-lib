open ell
open ellRefinement
open csr
open csrRefinement

pred sameMatrix [e: ELL, c: CSR, m: Matrix] {
  repInv[e]
  repInv[c]
  repInv[m]
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
    sameMatrix[e, c, m] and sameOrder[e, c] and m.rows > 0 and m.cols > 0 =>
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
        rv = rowvals[e, row],
        firstph = rc.idxOf[-1] {
      no firstph => {
        -- no placeholders, row is densely packed
        c.IA[add[row, 1]] = add[c.IA[row], e.maxnz]
        c.JA.subseq[row, add[row, e.maxnz]] = rc
        c.A.subseq[row, add[row, e.maxnz]] = rv
      } else firstph = 0 => {
        -- all placeholders, row is empty
        c.IA[add[row, 1]] = c.IA[row]
      } else {
        -- some placeholders, row is sparse
        let sidx = c.IA[row],           -- start index
            eidx = c.IA[add[row, 1]] {  -- end index
          eidx = add[sidx, firstph]
          c.JA.subseq[sidx, sub[eidx, 1]] = rc.subseq[0, sub[firstph, 1]]
          c.A.subseq[sidx, sub[eidx, 1]] = rv.subseq[0, sub[firstph, 1]]
        }
      }
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

pred showELLCSRslicing {
  some e: ELL, c: CSR, m: Matrix |
    sameMatrix[e, c, m] and ELLCSRslicing[e, c]
}

assert leftAlignedCSRslicing {
  all e: ELL, c: CSR, m: Matrix |
    sameMatrix[e, c, m] and leftAligned[e] => ELLCSRslicing[e, c]
}

run showLeftAligned for 8
run showELLCSRslicing for 10 but exactly 1 ELL, exactly 1 CSR, exactly 1 Matrix
check leftAlignedCSRslicing for 8 but exactly 1 ELL, exactly 1 CSR, exactly 1 Matrix

-----

pred showSame {
  some e: ELL, c: CSR, m: Matrix |
    m.rows > 0 and m.cols > 0 and
    sameMatrix[e, c, m] and sameOrder[e, c]
}

run showSame for 4 but exactly 1 ELL, exactly 1 CSR, exactly 1 Matrix

