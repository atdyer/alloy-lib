module expression

--open value
open matrix

sig Vector extends Matrix {} {
  all v: values[univ][univ] | v in Expression
}

--- matrix stuff
pred spmv [m: Matrix, v: Matrix, r: Vector] {

  -- matrix and vector are compatible
  m.cols = v.rows
  v.cols = 1

  -- result has same shape as vector
  r.rows = v.rows
  r.cols = v.cols

/**
  -- each row of the result vector is a single expression
  all i: Int {

    0 <= i and i <= r.rows => {

      let expr = r.values[row][0] {

        expr

      }

    }

  }
**/

}

pred show_spmv {
  some m, v: Matrix, r: Vector | 
    spmv[m, v, r] and
    m.rows = 2 and
    m.cols = 2 and 
    disj[m, v, r]
}

run show_spmv for 5 but exactly 3 Matrix, exactly 1 Vector
