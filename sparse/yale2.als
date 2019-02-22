module yale2

open matrix
open util/integer

sig Yale {
	rows: Int,
	cols: Int,
	A: seq Value,
	IA: seq Int,
	JA: seq Int
}

-----
----- Representation Invariant
-----

pred repInv [y: Yale] {

	-- the number of rows and columns >= 0
	y.rows >= 0
	y.cols >= 0

	-- there are no zeros stored as values
	Zero not in y.A.elems

	-- all index values: 0 <= i,j < rows, cols
	all i: y.IA.rest.elems | gte[i, 0] and lt[i, y.rows]
	all j: y.JA.elems      | gte[j, 0] and lt[j, y.cols]

	-- the first value of IA must always be zero
	y.IA[0] = 0

	-- the last value of IA must be equal to the length of A
	y.IA.last = #y.A

	-- all values of IA must be >= the previous value
	all i: y.IA.inds |
		i > 0 => y.IA[i] >= y.IA[sub[i, 1]]

	-- the last value of IA must not be repeated
	#y.IA > 1 => gt[y.IA.last, y.IA.butlast.last]

	-- A and JA must have the same length
	#y.A = #y.JA

	-- the maximum length of A is rows*cols
	lte[#y.A, mul[y.rows, y.cols]]

}

-----
----- Abstraction Function
-----

pred alpha [y: Yale, m: Matrix] {

	-- same number of rows and cols
	m.rows = y.rows
	m.cols = y.cols

	all i, j: Int {
		rowInRange[y, i] and
		colInRange[y, j] =>
			m.values[i][j] = get[y, i, j]
--		get[y, i, j] = v => m.values[i][j] = v
	}

}

-----
----- Helper functions/predicates
-----

pred rowInRange [y: Yale, row: Int] {
	0 <= row and row < y.rows
}

pred colInRange [y: Yale, col: Int] {
	0 <= col and col < y.cols
}

fun get [y: Yale, row, col: Int]: Value {

	-- a = IA[row]
	-- b = IA[row+1]
	let a = y.IA[row], b = y.IA[add[row, 1]] {

		-- if a or b is empty, zero
		-- if a = b, zero
		(no a or no b or a = b) => Zero else {

			-- j = JA[a, b)
			-- v = A[a, b)
			-- i = index of col in j
			let j = y.JA.subseq[a, sub[b, 1]],
			    v = y.A.subseq[a, sub[b, 1]],
				i = j.idxOf[col] {

				-- i is empty means zero, otherwise get value
				no i => Zero else v[i]

			}

		}

	}

}

-----
----- Checks
-----

assert valid {

	all m: Matrix |
		some y: Yale | alpha[y, m] -- and repInv[y]
--	all y: Yale |
--		repInv[y] => some m: Matrix | alpha[y, m]

}

check valid for 6

-----

pred show {
	all y: Yale | repInv[y] and y.rows = 0 and y.cols = 5
}

run show for 3 but 0 Matrix, exactly 1 Yale
