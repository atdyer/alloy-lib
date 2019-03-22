open yale

pred init0x0 {
  all m: Yale | initYale[m, 0, 0]
}

pred init1x1 {
  all m: Yale | initYale[m, 1, 1]
}

pred init2x2 {
  all m: Yale | initYale[m, 2, 2]
}

pred show0x0 {
  all m: Yale | m.rows = 0 and m.cols = 0 and repInv[m]
}

pred show1x1 {
  all m: Yale | m.rows = 1 and m.cols = 1 and repInv[m]
}

pred show2x2 {
  all m: Yale | m.rows = 2 and m.cols = 2 and repInv[m]
}

pred update1x1 {
  some m, m': Yale, row, col: Int, v: Value |
    initYale[m, 1, 1] and updateYale[m, m', row, col, v] and disj[m, m']
}

pred update2x2 {
  some m, m': Yale, row, col: Int, v: Value |
    initYale[m, 2, 2] and updateYale[m, m', row, col, v] and disj[m, m']
}

pred showExampleA {
  one m: Yale, a, b, c, d: Value-Zero {
    repInv[m]
    m.rows = 2
    m.cols = 2
    get[m, 0, 0] = a
    get[m, 0, 1] = b
    get[m, 1, 0] = c
    get[m, 1, 1] = d
    disj[a, b, c, d]
  }
}

fact { no Matrix }
run init0x0 for 1 but exactly 1 Yale
run init1x1 for 1 but exactly 1 Yale
run init2x2 for 1 but exactly 1 Yale
run show0x0 for 2 but exactly 1 Yale
run show1x1 for 2 but exactly 1 Yale
run show2x2 for 2 but exactly 1 Yale
run update1x1 for 2
run update2x2 for 2
run showExampleA for 5 but exactly 1 Yale