open yale

pred repInv [y: Yale] {
  Zero not in y.A.elems
  all i: y.IA.rest.elems | gte[i, 0] and lte[i, mul[y.rows, y.cols]]  -- IA values <= rows*cols
  all j: y.JA.elems | gte[j, 0] and lt[j, y.cols]                     -- JA values < cols
  y.IA[0] = 0
  y.IA.last = #y.A                               -- last value of IA is length of A
  #y.IA > 1 => gt[y.IA.last, y.IA.butlast.last]  -- last value of IA not repeated
  #y.A = #y.JA
  lte[#y.A, mul[y.rows, y.cols]]                 -- max length of A = rows*cols
  lte[#y.IA, add[y.rows, 1]]                     -- max length of IA = rows+1
  all i: y.IA.inds |
    i > 0 => let a = y.IA[sub[i, 1]],
                 b = y.IA[i],
                 n = sub[b, a] {
      b >= a                                -- values of IA increasing
      n <= y.cols                           -- max number of values in row
      #y.JA.subseq[a, sub[b, 1]].elems = n  -- column indices unique per row
    }
}

-- AX = B
-- A: mxn
-- X: nx1
-- B: mx1
pred spmv [A: Yale, X: Matrix, B: Matrix] {
  repInv[A]
  A.rows = B.rows
  A.cols = X.rows
  B.cols = 1
  X.cols = 1
  all i: Int {
    0 <= i and i < B.rows => {
      let a = A.IA[i],           -- start bounds for values in A
          b = A.IA[add[i, 1]],
          row = B.values[i][0] {  -- end bounds for values in A
        (no a or no b or a = b) => row = Zero else {
          -- build expression here
          -- row is a sum
          -- each expression in row is a product
          -- each product consists of A[i, j]*X[j, 0]
        }
      }
    }
  }
}

pred showSPMV {
  some A: Yale, x, b: Matrix | 
    spmv[A, x, b] and
    A.rows > 0 and
    A.cols > 0 -- and b.values[univ][univ] = Zero
}

run showSPMV for 5 but 0 Expression
