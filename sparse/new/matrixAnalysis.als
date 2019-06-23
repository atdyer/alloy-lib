open matrix

assert initValid {
  all m: Matrix, i, j: Int | 
    init[m, i, j] => repInv[m]
}

pred sparse [n: Int] { 
  one m: Matrix | 
    m.rows = n and 
    m.cols = n and 
    repInv[m] and
    all v: Value | v in m.values[univ][univ]
}

pred dense [n: Int] {
  one m: Matrix | 
    m.rows = n and 
    m.cols = n and 
    repInv[m] and
    m.values[Int][Int] = Value
}

-- bitwidth: [min, max]
--        4: [-8, 7]
--        5: [-16, 15]
--        6: [-32, 31]
--        7: [-64, 63]

-- initialization of empty sparse matrix preserves rep
-- invariant up to matrix size of 63x63
-- performance values using lingeling
check initValid for 7 Int  -- 10s + 5s

-- sparse matrices (at most half zeros), distinct value
-- performance values using lingeling
run s6x6 { sparse[6] } for 1 Matrix, exactly 18 Value
run s9x9 { sparse[8] } for 1 Matrix, exactly 40 Value, 5 Int  -- 1s + 10s

-- dense matrices, distinct values (allow one zero in matrix)
-- performance values using lingeling
run d2x2 { dense[2] } for 1 Matrix, exactly 4 Value
run d3x3 { dense[3] } for 1 Matrix, exactly 9 Value
run d4x4 { dense[4] } for 1 Matrix, exactly 16 Value
run d5x5 { dense[5] } for 1 Matrix, exactly 25 Value
run d6x6 { dense[6] } for 1 Matrix, exactly 36 Value
run d7x7 { dense[7] } for 1 Matrix, exactly 49 Value
run d8x8 { dense[8] } for 1 Matrix, exactly 64 Value, 5 Int  -- 2s + 5s
run d9x9 { dense[9] } for 1 Matrix, exactly 81 Value, 5 Int  -- 2s + 35s
