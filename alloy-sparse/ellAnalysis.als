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

-- up to 15 rows, 15 nonzero values
assert initValid {
  all e: ELL, i, j, n: Int |
    init[e, i, j, n] => repInv[e]
}
check initValid for 5 Int, 15 seq

