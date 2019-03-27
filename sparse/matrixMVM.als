open matrix
open sumprod

pred MVM [A, x, b: Matrix] {
  A.rows = b.rows
  A.cols = x.rows
  x.cols = 1
  b.cols = 1
  all i: Int {
    0 <= i and i < A.rows => {
      dotProd[A.values[i], x, b.values[i][0]]
    }
  }
}

pred dotProd [a: Int->Value, x: Matrix, b: SumProd] {
  all i: a.univ {
    b.values[i] = a[i]->x.values[i][0]
  }
  all i: Int - a.univ {
    no b.values[i]
  }
}

run {
  some A, x, b: Matrix {
    MVM[A, x, b]
    A.rows = 1
    A.cols = 1
    disj[A, x, b]
  }
} for 4 Int
