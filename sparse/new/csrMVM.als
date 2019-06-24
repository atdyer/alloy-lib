open csr
open sumprod
open csrRefinement
open matrixMVM

pred MVM [C: CSR, x, b: Matrix] {
  C.rows = b.rows
  C.cols = x.rows
  x.cols = 1
  b.cols = 1
  SumProd not in C.A.elems
  SumProd not in x.values[univ][univ]
  all i: rowInds[C] |
    let row = getrow[C, i] |
      dotProd[row, x, b.values[i][0]]
}

pred refines [C: CSR, M, x, Cb, Mb: Matrix] {
  repInv[C] and repInv[M] and 
  repInv[x] and repInv[Cb] and repInv[Mb] and
  alpha[C, M] and
  MVM[C, x, Cb] and
  MVM[M, x, Mb]
}

pred matEqv [a, b: Matrix] {
  a.rows = b.rows
  a.cols = b.cols
  all i: rowInds[a], j: colInds[a] |
    valEqv[a.values[i][j], b.values[i][j]]
}

pred somesize [n: Int] {
  some C: CSR, M, x, Cb, Mb: Matrix |
    C.rows = n and C.cols = n and
    refines[C, M, x, Cb, Mb] and matEqv[Cb, Mb]
}

pred allsize [n: Int] {
  all C: CSR, M, x, Cb, Mb: Matrix |
    C.rows = n and C.cols = n and
    refines[C, M, x, Cb, Mb] => matEqv[Cb, Mb]
}

/*
Check all 3x3 matrices with up to 6 unique values.
A 3x3 CSR matrix requires minimum bitwidth of 3 and
a minimum sequence length of 4. A 3x3 Matrix requires
a minimum bitwidth of 3.
No counterexample found.
10 seconds (lingeling)
*/
check c3x3 { allsize[3] } 
for exactly 1 CSR, exactly 4 Matrix, 9 Value, exactly 3 SumProd
run r3x3 { somesize[3] }
for exactly 1 CSR, exactly 4 Matrix, 9 Value, exactly 3 SumProd

/*
Check all 4x4 matrices with up to 6 unique values.
A 4x4 CSR matrix requires minimum bitwidth of 4 and
a minimum sequence length of 5. To hold 6 values, a
minimum sequence length of 6 is required.
No counterexample found.
32 seconds (lingeling)
*/
check c4x4 { allsize[4] }
for exactly 1 CSR, exactly 4 Matrix, 10 Value, exactly 4 SumProd, 7 seq

/*
Check all 5x5 matrices with up to n unique values.
A 5x5 CSR matrix requires minimum bitwidth of 4 and
a minimum sequence length of 6. A 5x5 Matrix requires
a minimum bitwidth of 4.
No counterexample found.
n = 5:  55 seconds (lingeling)
n = 10: 4 minutes (lingeling)
*/
check c5x5 { allsize[5] } 
for exactly 1 CSR, exactly 4 Matrix, 10 Value, exactly 5 SumProd, 7 seq
check c5x5 { allsize[5] } 
for exactly 1 CSR, exactly 4 Matrix, 15 Value, exactly 5 SumProd, 7 seq

