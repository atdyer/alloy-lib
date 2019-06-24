open csr

/**
Scope Notes:

As in Matrix, CSR values are indexed using integers, so
matrix size is limited by the bitwidth in the same way.
However, in CSR matrices, the IA sequence must be exactly
rows+1 values long. Therefore, the maximum number of rows
is limited by the maximum sequence length. By default,
Alloy uses bitwidth=4 and maxseq=4, meaning that the max
number of rows is 3. For a bitwidth of 4, the maximum
possible seq size is 7, allowing up to 6 rows. Be sure
to set the seq length (and int) to an appropriate value.
  Values and column indices are stored in a sequence as
well, and so the maximum total number of nonzero values
a CSR matrix can hold is equal to the maximum seq size.

The following is a table showing the Int ranges for
a given bitwidth:

int: [min, max]
  4: [-8, 7]
  5: [-16, 15]
  6: [-32, 31]
  7: [-64, 63]

*/


/*
Demonstrate that the maximum number of rows for a
bitwidth of 5 is 14 and the maximum number of nonzeros
that can be stored is 15.
  f14a - 14 rows, 15 nonzero, instance found
  f14b - 15 rows, 15 nonzero, no instance found
  f14c - 14 rows, 16 nonzero, no instance found
*/
pred fillrows [n: Int] {
  some c: CSR | 
    repInv[c] and 
    c.rows = n and 
    Value-Zero in c.A.elems
}
run f14a { fillrows[14] } for 5 Int, 15 seq, exactly 16 Value, 1 CSR, 0 Matrix
run f14b { fillrows[15] } for 5 Int, 15 seq, exactly 16 Value, 1 CSR, 0 Matrix
run f14c { fillrows[14] } for 5 Int, 15 seq, exactly 17 Value, 1 CSR, 0 Matrix


/*
Check that the init predicate does not violate the
rep invariant for matrices with up to 14 rows and
15 nonzero values.
*/
assert initValid {
  all c: CSR, i, j: Int |
    init[c, i, j] => repInv[c]
}
check initValid for 5 Int, 15 seq


/*
Verify that the get predicate returns a single value for
all valid indices and the empty set for all invalid
indices.
*/
assert getWorks {
  all c: CSR, i: rowInds[c], j: colInds[c] {
    repInv[c] => one get[c, i, j]
  }
  all c: CSR, i, j: Int {
    (repInv[c] and i not in rowInds[c]) => no get[c, i, j]
    (repInv[c] and j not in colInds[c]) => no get[c, i, j]
  }
}
check getWorks for 5 Int, 15 seq, 2 Value, 1 CSR, 0 Matrix


/*
Push the limits of the solver by attemping to fill a matrix
with as many values as possible.
  b14x15 - approx. 5 seconds (lingeling)
  b30x31 - approx. 4 minutes (lingeling)
*/
pred fillCSR [i, j: Int] {
  some c: CSR | 
    repInv[c] and c.rows = i and c.cols = j and Value-Zero in c.A.elems
}
run b14x15 { fillCSR[14, 15] } for 1 CSR, 0 Matrix, 15 seq, 5 Int, exactly 16 Value
run b30x31 { fillCSR[30, 31] } for 1 CSR, 0 Matrix, 31 seq, 6 Int, exactly 32 Value
