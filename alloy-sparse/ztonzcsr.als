open csr
open csrRefinement
open ztonzmatrix

pred ZtoNZ [c, c': CSR, i, j: Int, v: Value] {
  #c.A < #seq/Int      -- avoid maximum sequence length issues
  get[c, i, j] = Zero
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

-- example
run {
  some c, c': CSR, i, j: Int, v: Value |
    repInv[c] and
    ZtoNZ[c, c', i, j, v]
} for 0 Matrix, 2 CSR, 2 Value, 4 Int, 7 seq

-- preserve rep invariant
check {
  all c, c': CSR, i, j: Int, v: Value |
    repInv[c] and ZtoNZ[c, c', i, j, v] => repInv[c']
} for 0 Matrix, 2 CSR, 2 Value, 4 Int, 7 seq

-- data refinement
check {
  all c, c': CSR, m, m', m'': Matrix, i, j: Int, v: Value {
    repInv[c] and
    alpha[c, m] and 
    ZtoNZ[m, m', i, j, v] and
    ZtoNZ[c, c', i, j, v] and 
    alpha[c', m''] =>
      equivalent[m', m'']
  }
} for 3 Matrix, 2 CSR, 2 Value, 4 Int, 7 seq
