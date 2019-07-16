open csr
open sumprod
open matrixMVM
open csrRefinement

pred MVM [C: CSR, x: seq Value, b: seq SumProd] {
  C.rows = #b
  C.cols = #x
  all i: range[C.rows] |
    let row = getrow[C, i] |
      dotProd[row, x, b[i]]
}

pred refines [n: Int] {
  all C: CSR, M: Matrix, x: seq Value, Cb, Mb: seq SumProd |
    C.rows = n and C.cols = n and
    mulBoth[C, M, x, Cb, Mb] => vecEqv[Cb, Mb]
}

pred mulBoth [C: CSR, M: Matrix, x: seq Value, Cb, Mb: seq SumProd] {
  repInv[C]
  repInv[M]
  alpha[C, M]
  MVM[C, x, Cb]
  MVM[M, x, Mb]
}

pred vecEqv [a, b: seq SumProd] {
  #a = #b
  all i: a.inds |
    a[i].vals = b[i].vals
}


-- Check

-- ~5 seconds (lingeling)
check c3x3 { refines[3] } 
for exactly 1 CSR, exactly 1 Matrix, 9 Value, 6 SumProd, 4 seq

-- ~50 seconds (lingeling)
check c4x4 { refines[4] }
for exactly 1 CSR, exactly 1 Matrix, 16 Value, 8 SumProd, 5 seq


-- Show

pred somesize [n: Int] {
  some C: CSR, M: Matrix, x: seq Value, Cb, Mb: seq SumProd |
    C.rows = n and C.cols = n and
    mulBoth[C, M, x, Cb, Mb] and vecEqv[Cb, Mb]
}

run r3x3 { somesize[3] }
for exactly 1 CSR, exactly 1 Matrix, 9 Value, 6 SumProd, 4 seq

run r4x4 { somesize[4] }
for exactly 1 CSR, exactly 1 Matrix, 16 Value, 8 SumProd, 5 seq
