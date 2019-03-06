open yale

pred show0x0 {
  all m: Yale | initYale[m, 0, 0]
}

pred show1x1 {
  all m: Yale | initYale[m, 1, 1]
}

pred show2x2 {
  all m: Yale | initYale[m, 2, 2]
}

pred update1x1 {
  some m, m': Yale, row, col: Int, v: Value |
    initYale[m, 1, 1] and updateYale[m, m', row, col, v] and disj[m, m']
}

pred update2x2 {
  some m, m': Yale, row, col: Int, v: Value |
    initYale[m, 2, 2] and updateYale[m, m', row, col, v] and disj[m, m']
}

run show0x0 for 1 but exactly 1 Yale, 0 Matrix
run show1x1 for 1 but exactly 1 Yale, 0 Matrix
run show2x2 for 1 but exactly 1 Yale, 0 Matrix
run update1x1 for 2 but 0 Matrix
run update2x2 for 2 but 0 Matrix
