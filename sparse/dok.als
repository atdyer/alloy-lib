module dok

open matrix
open util/integer

sig DOK {
	rows: Int,
	cols: Int,
	dict: Int -> Int -> Value
}


-----
----- Operations
-----

pred init_dok [d: DOK, nrows, ncols: Int] {
	d.rows = nrows
	d.cols = ncols
	no d.dict
}

pred update_dok [d, d': DOK, row, col: Int, val: Value] {

	-- matrix size is the same
	d.rows = d'.rows
	d.cols = d'.cols

	-- indices are in range
	rowInRange[d, row]
	colInRange[d, col]

	-- allows all four cases
	let curr = d.dict[row][col] {
		(no curr and val != Zero and d'.dict = d.dict + row->col->val) or
		(no curr and val  = Zero and d'.dict = d.dict) or
		(val != Zero and d'.dict = d.dict - row->col->curr + row->col->val) or
		(val  = Zero and d'.dict = d.dict - row->col->curr)
	}

}

pred transpose_dok [d, d': DOK] {

	d'.rows = d.cols
	d'.cols = d.rows

	all i, j: Int | d.dict[i][j] = d'.dict[j][i]

}


-----
----- Helper predicates
-----

pred rowInRange [d: DOK, row: Int] {
	0 <= row and row < d.rows
}

pred colInRange [d: DOK, col: Int] {
	0 <= col and col < d.cols
}


-----
----- Abstraction function and rep invariant
-----

pred alpha [d: DOK, m: Matrix] {

	-- same number of rows and cols
	m.rows = d.rows
	m.cols = d.cols

	-- all dictionary values are in the matrix
	all i, j: Int, v: Value {
		i->j->v in d.dict => i->j->v in m.values
	}

	-- all others are zero in the matrix
	all i, j: Int {
		rowInRange[d, i] and
		colInRange[d, j] and
		i->j not in d.dict.univ => i->j->Zero in m.values
	}

}

pred repInv [d: DOK] {

	-- there are no zeros in the dict
	Zero not in d.dict[univ][univ]

	-- all row and col indices fall within bounds
	all i, j: Int {
		i->j in d.dict.univ =>
			rowInRange[d, i] and
			colInRange[d, j]
	}

	-- all row, col combinations may appear only once
	all i, j: Int {
		rowInRange[d, i] and
		colInRange[d, j] => 
			lone v: Value | i->j->v in d.dict
	}

}


-----
----- Assertions/Checks
-----

-- check that initial states do not violate the invariant
assert initValid {
	all d: DOK, i, j: Int | init_dok[d, i, j] => repInv[d]
}

check initValid for 5

-- check that updates do not violate the invariant
assert updateValid {
	all d, d': DOK, i, j: Int, v: Value {
		repInv[d] and update_dok[d, d', i, j, v] => repInv[d']
	}
}

check updateValid for 5

-- check that tranpose does not violate the invariant
assert transposeValid {
	all d, d': DOK {
		repInv[d] and transpose_dok[d, d'] => repInv[d']
	}
}

check transposeValid for 5

-- check for refinement
assert refines {

	all d, d': DOK, m, m': Matrix, i, j: Int, v: Value {

		init_dok[d, i, j] and alpha[d, m] => init[m, i, j]
		
		repInv[d]
		and update_dok[d, d', i, j, v] 
		and alpha[d, m] 
		and alpha[d', m'] => 
			update[m, m', i, j, v]

		repInv[d]
		and transpose_dok[d, d']
		and alpha[d, m]
		and alpha[d', m'] =>
			transpose[m, m'] 

	}

}

check refines for 5


-----
----- Examples
-----

-- a static example
pred show {

	-- a DOK and Matrix that represent the same matrix
	some d: DOK, m: Matrix | repInv[d] and alpha[d, m]

	-- an interesting case... the DOK actually has values
	#dict > 0

	-- keep things limited to a 2x2 matrix for simplicity
	all m: Matrix | m.rows = 2 and m.cols = 2
}

run show for exactly 1 DOK, exactly 1 Matrix, exactly 2 Value, 5 Int


-- an example that updates
pred show_update_dok {
	
	-- keep things limited to a 2x2 matrix for simplicity
	all m: Matrix | m.rows = 2 and m.cols = 2

	some d, d': DOK, m: Matrix | 
		disj[d, d'] and 
		repInv[d] and 
		repInv[d'] and 
		alpha[d, m] and 
		some v: Value |
			init_dok[d, 2, 2] and update_dok[d, d', 0, 0, v]

}

run show_update_dok for exactly 2 DOK, exactly 1 Matrix, exactly 2 Value, 5 Int


-- an example that transposes
pred show_transpose_dok {
	one d: DOK | d.rows = 3 and d.cols = 2 and #d.dict > 0
	some d, d': DOK |
		disj[d, d'] and repInv[d] and transpose_dok[d, d']
}

run show_transpose_dok for 2 DOK, 0 Matrix, exactly 4 Value, 5 Int
