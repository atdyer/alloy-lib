open ell

/**
Scope Notes:

As in matrix, ELL values are indexed using integers, so
matrix size is limited by bitwidth in the same way.
However, in ELL matrices, both the values and columns
sequences must be exactly rows*maxnz values long. This
governs the maximum number of nonzero values allowed in
the matrix.

The following is a table showing the Int ranges for
a given bitwidth:

int: [min, max]
  4: [-8, 7]
  5: [-16, 15]
  6: [-32, 31]
  7: [-64, 63]

*/

/*
Check that the init predicate does not violate the
rep invariant for matrices with up to 15 rows and
15 nonzero values.
*/
assert initValid {
  all e: ELL, i, j, n: Int |
    init[e, i, j, n] => repInv[e]
}
check initValid for 5 Int, 15 seq

/*
Verify that the get predicate returns a single value for
all valid indices and the empty set for all invalid
indices.
*/
assert getWorks {
  all e: ELL, i: rowInds[e], j: colInds[e] {
    repInv[e] => some get[e, i, j]
  }
  all e: ELL, i, j: Int {
    (repInv[e] and i not in rowInds[e]) => no get[e, i, j]
    (repInv[e] and j not in colInds[e]) => no get[e, i, j]
  }
}
check getWorks for 5 Int, 15 seq, 2 Value, 1 ELL, 0 Matrix

/*
Push the limits of the solver by attempting to fill a matrix
with as many values as possible.
*/
pred fillELL [i, j: Int] {
  some e: ELL |
    repInv[e] and e.rows = i and e.cols = j and Value in e.values.elems
}
run f15x15 { fillELL[15, 15] } for 1 ELL, 0 Matrix, 5 Int, 15 seq, exactly 15 Value
run f31x31 { fillELL[31, 31] } for 1 ELL, 0 Matrix, 6 Int, 31 seq, exactly 31 Value
