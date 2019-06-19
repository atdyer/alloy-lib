open ell

pred init0x0 {
  all e: ELL | initELL[e, 0, 0, 0]
}

pred init1x1x0 {
  all e: ELL | initELL[e, 1, 1, 0]
}

pred init1x1x1 {
  all e: ELL | initELL[e, 1, 1, 1]
}

pred init2x2x1 {
  all e: ELL | initELL[e, 2, 2, 1]
}

pred init2x2x2 {
  all e: ELL | initELL[e, 2, 2, 2]
}

pred show0x0 {
  all e: ELL | e.rows = 0 and e.cols = 0 and repInv[e]
}

pred show1x1 {
  all e: ELL | e.rows = 1 and e.cols = 1 and repInv[e]
}

pred show2x2 {
  all e: ELL | e.rows = 2 and e.cols = 2 and repInv[e]
}

pred update1x1 {
  some e, e': ELL, row, col: Int, v: Value |
    repInv[e] and disj[e, e'] and updateELL[e, e', row, col, v]
}

fact { no Matrix }
run init0x0 for 1 but exactly 1 ELL
run init1x1x0 for 1 but exactly 1 ELL
run init1x1x1 for 1 but exactly 1 ELL
run init2x2x1 for 2 but exactly 1 ELL
run init2x2x2 for 4 but exactly 1 ELL
run show0x0 for 1 but exactly 1 ELL
run show1x1 for 1 but exactly 1 ELL
run show2x2 for 4 but exactly 1 ELL
run update1x1 for 2
