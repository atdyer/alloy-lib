module matrix

open util/integer

sig Value {}
one sig Zero extends Value {}

sig Matrix {
	rows: Int,
	cols: Int,
	values: Int -> Int -> Value
} {

	-- number of rows and cols must be non-negative
	rows >= 0
	cols >= 0

	-- all values for row and col must fall within bounds
	all i, j: Int {
		i->j in values.univ =>
			0 <= i and i < rows and
			0 <= j and j < cols
	}

	-- number of values must be equal to rows*cols
	-- number of row, col pairs must be equal to rows*cols
	let nval = mul[rows, cols] {
		#values = nval
		#values.univ = nval
	}

}

-----
----- Operations
-----

pred init [m: Matrix, nrows, ncols: Int] {
	m.rows = nrows
	m.cols = ncols
	let valset = m.values[univ][univ] |
		valset = Zero or no valset      -- no valset needed for cases with 0 rows or cols
}

pred update [m, m': Matrix, row, col: Int, val: Value] {
	m.rows = m'.rows
	m.cols = m'.cols
	rowInRange[m, row]
	colInRange[m, col]
	let curr = m.values[row][col] |
		m'.values = m.values - row->col->curr + row->col->val
}

pred transpose [m, m': Matrix] {
	m'.rows = m.cols
	m'.cols = m.rows
	all i, j: Int | m.values[i][j] = m'.values[j][i]
}

-- all values are part of a matrix
-- fact { all v: Value | v in values[univ][univ][univ] }

-----
----- Helper predicates
-----

pred rowInRange [m: Matrix, row: Int] {
	0 <= row and row < m.rows
}

pred colInRange [m: Matrix, col: Int] {
	0 <= col and col < m.cols
}

-----
----- Checks and Runs
-----

-- create an empty 2x2 matrix
pred show {
	all m: Matrix | init[m, 2, 2]
}

run show for 1 Matrix, 5 Value, 5 Int


-- create an empty 2x2 matrix and update it with a value
pred show_update {
	some m, m': Matrix, row, col: Int, v: Value |
		disj[m, m'] and init[m, 2, 2] and update[m, m', row, col, v]
}

run show_update for 2 Matrix, 5 Value, 5 Int


-- tranpose a 2x3 or 3x2 matrix
pred show_transpose {
	one m: Matrix | m.rows = 3 and m.cols = 2
	some m, m': Matrix |
		disj[m, m'] and transpose[m, m']
}

run show_transpose for 2 Matrix, exactly 4 Value, 5 Int
