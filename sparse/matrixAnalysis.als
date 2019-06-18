open matrix

pred show0x0 {
  all m: Matrix | init[m, 0, 0]
}

pred show1x1 {
  all m: Matrix | init[m, 1, 1]
}

pred show2x2 {
  all m: Matrix | init[m, 2, 2]
}

pred update1x1 {
  some m, m': Matrix, row, col: Int, v: Value |
    init[m, 1, 1] and update[m, m', row, col, v] and disj[m, m']
}

pred update2x2 {
  some m, m': Matrix, row, col: Int, v: Value |
    init[m, 2, 2] and update[m, m', row, col, v] and disj[m, m']
}

run show0x0 for 1 but exactly 1 Matrix
run show1x1 for 1 but exactly 1 Matrix
run show2x2 for 1 but exactly 1 Matrix
run update1x1 for 2
run update2x2 for 2
