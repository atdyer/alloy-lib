open matrix

assert initValid {
  all m: Matrix, i, j: Int | 
    init[m, i, j] => repInv[m]
}

pred init0x0 { all m: Matrix | init[m, 0, 0] }
pred init1x1 { all m: Matrix | init[m, 1, 1] }
pred init2x2 { all m: Matrix | init[m, 2, 2] }
pred show0x0 { all m: Matrix | m.rows = 0 and m.cols = 0 and repInv[m] }
pred show1x1 { all m: Matrix | m.rows = 1 and m.cols = 1 and repInv[m] }
pred show2x2 { all m: Matrix | m.rows = 2 and m.cols = 2 and repInv[m] }

check initValid for 5
run init0x0 for 1 but exactly 1 Matrix
run init1x1 for 2 but exactly 1 Matrix
run init2x2 for 2 but exactly 1 Matrix
run show0x0 for 1 but exactly 1 Matrix
run show1x1 for 2 but exactly 1 Matrix
run show2x2 for 2 but exactly 1 Matrix
