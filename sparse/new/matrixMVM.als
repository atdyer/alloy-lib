open matrix
open sumprod

-- Ax = b
pred MVM [A, x, b: Matrix] {
  A.rows = b.rows
  A.cols = x.rows
  x.cols = 1
  b.cols = 1
  SumProd not in A.values[univ][univ]
  SumProd not in x.values[univ][univ]
  all i: rowInds[A] |
    dotProd[A.values[i], x, b.values[i][0]]
}

-- b = dot(row, x)
pred dotProd [row: Int->Value, x: Matrix, b: SumProd] {
  all col: row.univ |
    b.values[col] = row[col]->x.values[col][0]
  all col: Int - row.univ |
    no b.values[col]
}

pred dpnew [row: Int->Value, x: Matrix, b: SumProd] {

}

-- generate ixj MVM, force all values into matrix
pred show [i, j: Int] {
  some A, x, b: Matrix |
    repInv[A] and
    repInv[x] and
    repInv[b] and
    A.rows = i and
    A.cols = j and
    Value-SumProd in A.values[univ][univ] and
    disj[A, x, b] and
    MVM[A, x, b]
}

run s5x5x10 { show[5, 5] } for exactly 3 Matrix, exactly 10 Value  -- ~5sec
run s5x5x25 { show[5, 5] } for exactly 3 Matrix, exactly 25 Value  -- ~40sec
run s8x8x10 { show[8, 8] } for exactly 3 Matrix, exactly 10 Value, 5 Int -- ~10sec
run s8x8x15 { show[8, 8] } for exactly 3 Matrix, exactly 15 Value, 5 Int -- ~20sec
run s8x8x20 { show[8, 8] } for exactly 3 Matrix, exactly 20 Value, 5 Int -- ~50sec
