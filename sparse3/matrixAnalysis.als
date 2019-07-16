open matrix

/**
Scope Notes:

For Matrix, the number of values stored is limited by the
indexing per dimension. Alloy by default sets the bitwidth
to 4, so the maximum number of rows or columns is 7 (or
rather, the maximum matrix size is 7x7), meaning that at
most 49 values can be stored. Increasing the bitwidth will 
increase the allowable matrix size. So setting the bitwidth
to 5 allows for dimensions to be up to size 15, meaning
a matrix can store 225 values.
  The number of unique values that can be stored in a 
matrix is limited by Alloy. The most I have been able to
generate without raising a "translation capacity exceeded"
error is 182 using the command:

  run { fill[15] } for 1 Matrix, exactly 182 Value, 5 Int

The following is a table showing the Int ranges for
a given bitwidth:

int: [min, max]
  4: [-8, 7]
  5: [-16, 15]
  6: [-32, 31]
  7: [-64, 63]

*/


/*
The fill predicate creates an nxn matrix and forces
all existing values to appear in that matrix
*/
pred fill [n: Int] { 
  some m: Matrix | 
    m.rows = n and 
    m.cols = n and 
    repInv[m] and
    Value in m.values[univ][univ]
}

/*
Check that the init predicate does not violate the rep
invariant for matrices with up to 63 rows and cols
*/
assert initValid {
  all m: Matrix, i, j: Int | 
    init[m, i, j] => repInv[m]
}
check initValid for exactly 1 Matrix, 2 Value, 7 Int

/*
Push the limits of the solver by attempting to fill a
matrix with as many unique values as possible
*/
run m2x2 { fill[2] } for 1 Matrix, exactly 4 Value
run m3x3 { fill[3] } for 1 Matrix, exactly 9 Value
run m4x4 { fill[4] } for 1 Matrix, exactly 16 Value
run m5x5 { fill[5] } for 1 Matrix, exactly 25 Value
run m6x6 { fill[6] } for 1 Matrix, exactly 36 Value
run m7x7 { fill[7] } for 1 Matrix, exactly 49 Value
run m8x8 { fill[8] } for 1 Matrix, exactly 64 Value, 5 Int  -- 2s + 5s
run m9x9 { fill[9] } for 1 Matrix, exactly 81 Value, 5 Int  -- 2s + 35s

