module yale

open matrix
open util/integer

sig Yale {
	rows: Int,
	cols: Int,
	A: seq Value - Zero,
	IA: seq Int,
	JA: seq Int
}

-----
----- Operations
-----

pred init_yale [y: Yale, nrows, ncols: Int] {
	y.rows = nrows
	y.cols = ncols
	no y.A
	no y.JA
	y.IA = 0->0
}

pred update [y, y': Yale, row, col: Int, val: Value] {

	-- matrix size stays the same
	y'.rows = y.rows
	y'.cols = y.cols

	-- indices are in range
	rowInRange[y, row]
	colInRange[y, col]

	let curr = getValue[y, row, col] {
--		curr != Zero and val != Zero and update_existing[y, y', row, col, val]
		curr != Zero and val = Zero and remove_existing[y, y', row, col]
	}

}

-- Change nonzero value to another nonzero value
pred update_existing [y, y': Yale, row, col: Int, val: Value] {

	y'.IA = y.IA
	y'.JA = y.JA

	let start = y.IA[row],
	    end   = y.IA[add[row,1]],
	    JAsub = y.JA.subseq[start, sub[end, 1]],
	    index = add[start, JAsub.idxOf[col]] {

		y'.A = y.A.setAt[index, val]

	}

}


pred remove_existing [y, y': Yale, row, col: Int] {

	let start = y.IA[row],
	    end   = y.IA[add[row, 1]],
			JAsub = y.JA.subseq[start, sub[end, 1]],
	    index = add[start, JAsub.idxOf[col]] {

		-- all IA leading up to end remain the same
		-- all IA including and after end subtract one
		y'.JA = y.JA.delete[index]
		y'.A  =  y.A.delete[index]

		-- all indices up to and including the start index for this row remain the same
		y'.IA.subseq[0, row] = y.IA.subseq[0, row]

		-- all indices including and after the end index for this row subtract one
		let endIndex = add[row, 1],
		    IAlength = y.IA.lastIdx {
			
			-- if the end index is the last value in the IA array, simply remove it
			(endIndex = IAlength and y'.IA = y.IA.delete[endIndex]) or

			subEach[
				y .IA.subseq[endIndex, IAlength],
				y'.IA.subseq[endIndex, IAlength],
				1
			]

		}

	}

}


-----
----- Helper predicates
-----

pred rowInRange [y: Yale, row: Int] {
	0 <= row and row < y.rows
}

pred colInRange [y: Yale, col: Int] {
	0 <= col and col < y.cols
}

-- s' is the sequence in which n is added to each value in sequence s
pred addEach [s, s': seq Int, n: Int] {

	s.inds = s'.inds

	all i: s.inds | s'[i] = add[s[i], n]

}

-- s' is the sequence in which n is subtracted from each value in sequence s
pred subEach [s, s': seq Int, n: Int] {

	s.inds = s'.inds

	all i: s.inds | s'[i] = sub[s[i], n]

}

-- get the value in the matrix
fun getValue [y: Yale, row, col: Int]: Value {

	let start = y.IA[row],
	    end   = y.IA[add[row, 1]] {

		-- if either start or end is empty, the value is zero
		(no start or no end) => Zero else {
			
			let nvals = sub[end, start],
			    JAsub = y.JA.subseq[start, sub[end, 1]],
			     Asub =  y.A.subseq[start, sub[end, 1]] {

				-- if there are no values on this row, the value is zero
				nvals = 0 => Zero else {

					let index = JAsub.idxOf[col] {

						no index => Zero else Asub[index]

					}

				}

			}

		}

	}

}

-----
----- Checks and Runs
-----

pred show {
	#Matrix = 0
	#Yale = 1
	all y: Yale | init_yale[y, 2, 2]
}

sig Five, Eight, Three, Six extends Value {}

/*
An example matrix from the sparse matrix wikipedia page

0 0 0 0
5 8 0 0
0 0 3 0
0 6 0 0

*/
pred wiki {
	#Matrix = 0
	#Yale = 2
	one y: Yale {
		y.rows = 4
		y.cols = 4
		#y.A = 4
		#y.IA = 5
		#y.JA = 4
		y.A[0] = Five
		y.A[1] = Eight
		y.A[2] = Three
		y.A[3] = Six
		y.IA[0] = 0
		y.IA[1] = 0
		y.IA[2] = 2
		y.IA[3] = 3
		y.IA[4] = 4
		y.JA[0] = 0
		y.JA[1] = 1
		y.JA[2] = 2
		y.JA[3] = 1
	}
	some y, y': Yale | update[y, y', 3, 1, Zero]
}

run wiki for 5

assert getWorks {
	wiki => all y: Yale {
		getValue[y, 0, 0] = Zero
		getValue[y, 0, 1] = Zero
		getValue[y, 0, 2] = Zero
		getValue[y, 0, 3] = Zero

		getValue[y, 1, 0] = Five
		getValue[y, 1, 1] = Eight
		getValue[y, 1, 2] = Zero
		getValue[y, 1, 3] = Zero

		getValue[y, 2, 0] = Zero
		getValue[y, 2, 1] = Zero
		getValue[y, 2, 2] = Three
		getValue[y, 2, 3] = Zero

		getValue[y, 3, 0] = Zero
		getValue[y, 3, 1] = Six
		getValue[y, 3, 2] = Zero
		getValue[y, 3, 3] = Zero
	}
}

check getWorks for 5
