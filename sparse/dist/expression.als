module expression

--open value
open matrix

sig Vector extends Matrix {} {
  cols = 1
}

--- matrix stuff
pred spmv [m: Matrix, v: Vector, r: Vector] {

  -- matrix and vector are compatible
  m.cols = v.rows

  -- result has same shape as vector
  r.rows = v.rows
  r.cols = v.cols

  -- no expressions in v
  all x: v.values[univ][univ] | x not in Expression

  -- all r values are Sums
  all x: r.values[univ][univ] | x in Sum

  -- i = current row
  -- j = current column
  all i, j: Int {
    0 <= i and i <= m.rows and
    0 <= j and j <= v.rows => {
      let A = m.values[i][j],    -- A = matrix[i][j]
          b = v.values[i][0],    -- b = vector[i]
          s = r.values[i][0] {   -- s = result[i] (a Sum)
        some p: Product {
          p.variables = A + b
          p in s.variables
        }
      }
    }
  }
}

pred show_spmv {
  some m, v: Matrix, r: Vector | 
    spmv[m, v, r] and
    m.rows = 2 and
    m.cols = 2 and 
    disj[m, v, r]
}

pred show_vector {
  some m: Matrix, v: Vector {
    m.rows > 0
    m.cols > 0
    m.cols = v.rows
  }
}

run show_spmv for 5 but exactly 3 Matrix, exactly 1 Vector
run show_vector for 5 but exactly 2 Matrix, exactly 1 Vector
