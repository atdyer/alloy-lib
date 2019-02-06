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
		valset = Zero or no valset
}

pred update [m, m': Matrix, row, col: Int, val: Value] {
	m.rows = m'.rows
	m.cols = m'.cols
	0 <= row and row < m.rows
	0 <= col and col < m.cols
	let curr = m.values[row][col] |
		m'.values = m.values - row->col->curr + row->col->val
}

-- all values are part of a matrix
-- fact { all v: Value | v in values[univ][univ][univ] }

-----
----- Checks and Runs
-----

pred show {
	all m: Matrix | init[m, 2, 2]
}

run show for 1 Matrix, 5 Value, 5 Int

pred show_update {
	some m, m': Matrix, row, col: Int, v: Value |
		disj[m, m'] and init[m, 2, 2] and update[m, m', row, col, v]
}

run show_update for 2 Matrix, 5 Value, 5 Int
