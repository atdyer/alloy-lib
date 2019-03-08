module spmv

open expression
open matrix

sig Vector extends Matrix {} {
  cols = 1
}

