open ell
open ellRefinement
open csr
open csrRefinement
open util/integer

-- full sequence of kpos values
pred genkpos [e: ELL, kpos: seq Int] {
  kpos[0] = 0
  #kpos = e.rows.mul[e.maxnz].add[1]
  all i: rowInds[e] {
    all k: indices[e.maxnz] {
      let idx = i.mul[e.maxnz].add[k] {
        rowcols[e, i][k] != -1 => {
          it < kpos.lastIdx => kpos[idx.add[1]] = kpos[idx].add[1]
        } else {
          it < kpos.lastIdx => kpos[idx.add[1]] = kpos[idx]
        }
      }
    }
  }
}

pred next [e, e': ELL, idx, kpos: Int] {
  e.rows = e'.rows
  e.cols = e'.cols
  e.maxnz = e'.maxnz
  idx != kpos => {
    e'.values = e.values.setAt[kpos, e.values[idx]]
    e'.columns = e.columns.setAt[kpos, e.columns[idx]]
  } else {
    e'.values = e.values
    e'.columns = e.columns
  }
}

pred ellcsrip [e: ELL, c: CSR] {
  e.rows = c.rows
  e.cols = c.cols
  c.IA[0] = 0
  some kpos: seq Int, es: seq ELL, elast: ELL {
    genkpos[e, kpos]
    es.last = elast
    all idx: indices[e.rows.mul[e.maxnz]]
      next[e[idx], e[idx.add[1]], idx, kpos[idx]]
    }
  }
}

pred isCSR [e: ELL, c: CSR] {
  repInv[c]
  c.A = e.values.subseq[0, c.IA.last]
  c.JA = e.columns.subseq[0, c.IA.last]
}
