open ell
open ellRefinement
open csr
open csrRefinement
open util/integer

pred ellcsr [e: ELL, c: CSR] {
  e.rows = c.rows
  e.cols = c.cols
  c.IA[0] = 0
  #c.IA = c.rows.add[1]
  some kpos: seq Int {
    kpos[0] = 0
    #kpos = e.rows.mul[e.maxnz].add[1]
    #c.A = kpos.last
    #c.JA = kpos.last
    all i: range[e.rows] {
      all k: range[e.maxnz] {
        let kp = i.mul[e.maxnz].add[k], kp' = kp.add[1] {
          rowcols[e, i][k] != -1 => {
            c.A[kp] = rowvals[e, i][k]
            c.JA[kp] = rowcols[e, i][k]
            kpos[kp'] = kpos[kp].add[1]
          } else {
            kpos[kp'] = kpos[kp]
          }
        }
      }
      c.IA[i.add[1]] = kpos[i.add[1].mul[e.maxnz]]
    }
  }
}

pred interesting [e: ELL] {
  e.rows > 1
  e.cols > 1
  e.maxnz > 1
  repInv[e]
  some v: (Value-Zero) | v in e.vals.elems
}

check {
  all e: ELL, c: CSR |
    repInv[e] and ellcsr[e, c] => repInv[c]
} for 4 Int, 7 seq, 0 Matrix, 1 ELL, 1 CSR, 2 Value 

check {
  all e: ELL, c: CSR, m: Matrix {
    repInv[e] and alpha[e, m] and ellcsr[e, c] => alpha[c, m] and repInv[c]
  }
} for 4 Int, 7 seq, 1 Matrix, 1 ELL, 1 CSR, 2 Value

run {
  some e: ELL, c: CSR |
    interesting[e] and ellcsr[e, c]
} for 4 Int, 7 seq, 0 Matrix, 1 ELL, 1 CSR, 2 Value

//open util/ordering[State] as so

//sig State {
//  i, k, kpos: Int
//}
//
//pred ellcsr [e: ELL, c: CSR] {
//  e.rows = c.rows
//  e.cols = c.cols
//  c.IA[0] = 0
//  #c.IA = c.rows + 1
//  some kpos: seq Int {
//    #c.A = kpos.last
//    #c.JA = kpos.last
//    all i: range[e.rows] {
//      all j: range[e.cols] {
//        rowcols[e, i][k] != -1 =>
//      }
//    }
//  }
//}
//
//pred ellcsr [e: ELL, c, c': CSR, i, k: Int] {
//  
//}
//
//pred initial [s: State] {
//  s.i = 0
//  s.k = 0
//  s.kpos = 0
//}
//
//pred next [s, s': State, e: ELL] {
//  s.k = e.maxnz => s'.i = s.i + 1 else s.i
//  s'.k = rem[s.k + 1, e.maxnz]
//}
