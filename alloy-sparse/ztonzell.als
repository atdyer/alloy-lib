open ell
open ellRefinement
open ztonzmatrix

pred ZtoNZ [e, e': ELL, i, j: Int, v: Value] {
  get[e, i, j] = Zero
  v != Zero
  e'.rows = e.rows
  e'.cols = e.cols
  e'.maxnz = e.maxnz
  let a = i.mul[e.maxnz],
      b = a.add[e.maxnz] {
    one k: range[a, b] {
      e.cids[k] = -1
      e'.vals = e.vals ++ k->v
      e'.cids = e.cids ++ k->j
    }
  }
}

-- example
run {
  some e, e': ELL, i, j: Int, v: Value |
    repInv[e] and ZtoNZ[e, e', i, j, v]
} for 0 Matrix, 2 ELL, 3 Value, 4 Int, 7 seq

-- preserve rep invariant
check {
  all e, e': ELL, i, j: Int, v: Value |
    repInv[e] and ZtoNZ[e, e', i, j, v] => repInv[e']
} for 0 Matrix, 2 ELL, 3 Value, 4 Int, 7 seq

-- data refinement
check {
  all e, e': ELL, m, m', m'': Matrix, i, j: Int, v: Value {
    repInv[e] and
    alpha[e, m] and
    ZtoNZ[m, m', i, j, v] and
    ZtoNZ[e, e', i, j, v] and
    alpha[e', m''] =>
      equivalent[m', m'']
  }
} for 3 Matrix, 2 ELL, 5 Value, 4 Int, 7 seq
