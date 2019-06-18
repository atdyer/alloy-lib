module ell

open matrix
open util/integer

sig ELL {
  nrows, ncols: Int,
  maxnz: Int,
  vals: seq Value,
  cols: seq Int
} {
  nrows >= 0
  ncols >= 0
}

pred repInv [e: ELL] {
  #e.vals = mul[e.nrows, e.maxnz]
}

pred show {
  all e: ELL | e.maxnz > 0 and e.nrows > 1 and repInv[e]
}

run show for 2 but 1 ELL, 0 Matrix
