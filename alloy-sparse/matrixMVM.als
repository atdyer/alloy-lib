open matrix
open sumprod

pred MVM [A: Matrix, x: seq Value, b: seq SumProd] {
  A.rows = #b
  A.cols = #x
  all i: range[A.rows] |
    dotProd[A.vals[i], x, b[i]]
}

pred dotProd [row: Int->Value, x: seq Value, b: SumProd] {
  b.vals = { i: row.univ, j, k: Value-Zero | j = row[i] and k = x[i] }
}

pred show [i, j: Int] {
  some A: Matrix, x: seq Value, b: seq SumProd |
    repInv[A] and
    A.rows = i and
    A.cols = j and
    MVM[A, x, b]
}

-- SAT4J
run s5x5x10 { show[5, 5] } for exactly 1 Matrix, exactly 10 Value, 5 SumProd, 5 seq  -- <1sec
run s5x5x25 { show[5, 5] } for exactly 3 Matrix, exactly 25 Value, 5 SumProd, 5 seq  -- ~10sec
run s8x8x10 { show[8, 8] } for exactly 3 Matrix, exactly 10 Value, 5 Int, 8 SumProd, 8 seq -- ~14sec
run s8x8x15 { show[8, 8] } for exactly 3 Matrix, exactly 15 Value, 5 Int, 8 SumProd, 8 seq -- ~35sec
