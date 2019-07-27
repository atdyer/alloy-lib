open ell
open ellRefinement
open ztonzmatrix

pred update [e, e': ELL, i, j: Int, v: Value] {
  inrange[e, i, j]
  e'.rows = e.rows
  e'.cols = e.cols
  e'.maxnz = e.maxnz
  let a = i.mul[e.maxnz],
      b = a.add[e.maxnz],
      l = v = Zero => -1 else j {
    (some k: range[a, b] | e.cids[k] = j) => {
      let k = e.cids.j {
        k in range[a, b]
        e'.vals = e.vals ++ k->v
        e'.cids = e.cids ++ k->l
      }
    } else
    one k: range[a, b] {
      e.cids[k] = -1
      e'.vals = e.vals ++ k->v
      e'.cids = e.cids ++ k->l
    }
  }
}

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
    repInv[e] and update[e, e', i, j, v] and disj[e, e']
} for 0 Matrix, 2 ELL, 3 Value, 4 Int, 7 seq

-- preserve rep invariant
check {
  all e, e': ELL, i, j: Int, v: Value |
    repInv[e] and update[e, e', i, j, v] => repInv[e']
} for 0 Matrix, 2 ELL, 3 Value, 4 Int, 7 seq

-- data refinement
check {
  all e, e': ELL, m, m', m'': Matrix, i, j: Int, v: Value {
    repInv[e] and
    alpha[e, m] and
    update[m, m', i, j, v] and
    update[e, e', i, j, v] and
    alpha[e', m''] =>
      equivalent[m', m'']
  }
} for 3 Matrix, 2 ELL, 5 Value, 4 Int, 7 seq

check {
  all e, e': ELL, m, m': Matrix, i, j: Int, v: Value {
    repInv[e] and
    alpha[e, m] and
    update[m, m', i, j, v] and
    update[e, e', i, j, v] =>
      alpha[e', m']
  }
} for 2 Matrix, 2 ELL, 5 Value, 4 Int, 7 seq

check {
  all e, e': ELL, m, m': Matrix, i, j: Int, v: Value {
    repInv[e] and
    update[e, e', i, j, v] and
    alpha[e, m] and
    alpha[e', m'] =>
      update[m, m', i, j, v]
  }
} for 2 Matrix, 2 ELL, 5 Value, 4 Int, 7 seq
