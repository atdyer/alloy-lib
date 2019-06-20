open ell

/*
Assert that the initialization predicate
satisfies the representation invariant for
all matrix sizes.
*/
assert initValid {
  all e: ELL, i, j, z: Int |
    init[e, i, j, z] => repInv[e]
}

/*
Assert that the get function works as expected.
Using valid indices will always return a value,
and invalid indices will always return the
empty set.
*/
assert getWorks {
  all e: ELL, i: rowInds[e], j: colInds[e] {
    repInv[e] => some get[e, i, j]
  }
  all e: ELL, i: Int-rowInds[e], j: Int-colInds[e] {
    repInv[e] => no get[e, i, j]
  }
}

check initValid for 5
check getWorks for 5 but 0 Matrix


/*
View ELL matrices in various valid states
*/
pred init0x0x0 { all e: ELL | init[e, 0, 0, 0] }
pred init1x1x0 { all e: ELL | init[e, 1, 1, 0] }
pred init1x1x1 { all e: ELL | init[e, 1, 1, 1] }
pred init2x2x0 { all e: ELL | init[e, 2, 2, 0] }
pred init2x2x1 { all e: ELL | init[e, 2, 2, 1] }
pred init2x2x2 { all e: ELL | init[e, 2, 2, 2] }
pred show0x0x0 { all e: ELL | 
  e.rows = 0 and e.cols = 0 and e.maxnz = 0 and repInv[e] }
pred show1x1x1 { all e: ELL | 
  e.rows = 1 and e.cols = 1 and e.maxnz = 1 and repInv[e] }
pred show2x2x2 { all e: ELL | 
  e.rows = 2 and e.cols = 2 and e.maxnz = 2 and repInv[e] }
run init0x0x0 for 1 but exactly 1 ELL, 0 Matrix
run init1x1x0 for 2 but exactly 1 ELL, 0 Matrix
run init1x1x1 for 2 but exactly 1 ELL, 0 Matrix
run init2x2x0 for 3 but exactly 1 ELL, 0 Matrix
run init2x2x1 for 3 but exactly 1 ELL, 0 Matrix
run init2x2x2 for 3 but exactly 1 ELL, 0 Matrix
run show0x0x0 for 1 but exactly 1 ELL, 0 Matrix
run show1x1x1 for 2 but exactly 1 ELL, 0 Matrix
run show2x2x2 for 4 but exactly 1 ELL, 0 Matrix
