open csr

/*
Assert that the initialization predicate
satisfies the representation invariant for
all matrix sizes.
*/
assert initValid {
  all c: CSR, i, j: Int |
    init[c, i, j] => repInv[c]
}

/*
Assert that the get function works as expected.
Using valid indices will always return a value,
and invalid indices will always return the
empty set.
*/
assert getWorks {
  all c: CSR, i: rowInds[c], j: colInds[c] {
    repInv[c] => some get[c, i, j]
  }
  all c: CSR, i: Int-rowInds[c], j: Int-colInds[c] {
    repInv[c] => no get[c, i, j]
  }
}

check initValid for 5
check getWorks for 5 but 0 Matrix


/*
View CSR matrices in various valid states
*/
pred init0x0 { all c: CSR | init[c, 0, 0] }
pred init1x1 { all c: CSR | init[c, 1, 1] }
pred init2x2 { all c: CSR | init[c, 2, 2] }
pred show0x0 { all c: CSR | c.rows = 0 and c.cols = 0 and repInv[c] }
pred show1x1 { all c: CSR | c.rows = 1 and c.cols = 1 and repInv[c] }
pred show2x2 { all c: CSR | c.rows = 2 and c.cols = 2 and repInv[c] }
run init0x0 for 1 but exactly 1 CSR, 0 Matrix
run init1x1 for 2 but exactly 1 CSR, 0 Matrix
run init2x2 for 3 but exactly 1 CSR, 0 Matrix
run show0x0 for 1 but exactly 1 CSR, 0 Matrix
run show1x1 for 2 but exactly 1 CSR, 0 Matrix
run show2x2 for 4 but exactly 1 CSR, 0 Matrix
