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
  #a = #x.values
  #a = #b.values
  all i: Int {
    0 <= i and i < #a => {
      let product = b.values[i] {
        product = a[i]->x.values[i][0]
      }
    }
  }
}

run {
  some A, x, b: Matrix | 
    MVM[A, x, b] 
    and A.rows > 0 
    and A.cols > 0
    and disj[A, x, b]
} for 3
