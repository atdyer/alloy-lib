open csr
open csrRefinement

pred ZtoNZ [c, c': CSR, i, j: Int, v: Value] {
  #c.A < #seq/Int      -- avoid maximum sequence length issues
  get[c, i, j] = Zero  -- i, j validity checks done here
  v != Zero
  c'.rows = c.rows
  c'.cols = c.cols

  c'.A = c.A.insert[c.IA[i], v]
  c'.JA = c.JA.insert[c.IA[i], j]

  #c'.IA = #c.IA
  c'.IA.subseq[0, i] = c.IA.subseq[0, i]
  all n: range[i.add[1], c.rows.add[1]] {
    c'.IA[n] = c.IA[n].add[1]
  }
}

pred ZtoNZ[m, m': Matrix, i, j: Int, v: Value] {
  m.vals[i][j] = Zero
  v != Zero
  m'.rows = m.rows
  m'.cols = m.cols
  let u = m.vals[i][j] |
    m'.vals = m.vals - i->j->u + i->j->v
}

run {
  some c, c': CSR, i, j: Int, v: Value |
    repInv[c] and
    ZtoNZ[c, c', i, j, v]
} for 2 CSR, 0 Matrix, 3 Value

-- preserve abstract rep invariant
check {
  all m, m': Matrix, i, j: Int, v: Value |
    repInv[m] and ZtoNZ[m, m', i, j, v] => repInv[m']
} for 2 Matrix, 0 CSR, 5 Value

-- preserve CSR rep invariant
check {
  all c, c': CSR, i, j: Int, v: Value |
    repInv[c] and ZtoNZ[c, c', i, j, v] => repInv[c']
} for 0 Matrix, 2 CSR, 5 Value, 5 seq

-- data refinement
check {
  all c, c'': CSR, m, m', m'': Matrix, i, j: Int, v: Value {
    repInv[c] and
    alpha[c, m] and ZtoNZ[m, m', i, j, v] and
    ZtoNZ[c, c'', i, j, v] and alpha[c'', m''] =>
      equivalent[m', m'']
  }
} for 3 Matrix, 2 CSR, 5 Value, 5 seq
