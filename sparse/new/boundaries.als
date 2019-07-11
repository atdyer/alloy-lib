open matrix

/*
From ADCIRC documentation, for boundary nodes:
- set on-diagonal terms equal to RMS of all diagonals
- zero all off-diagonal terms in the row
- zero all off-diagonal terms in column
- save all off-diagonal nonzero terms in column
*/

-- Value representing RMS of all diagonal terms
sig RMS extends Value {}

-- Dictionary that can only store nonzero and not RMS values
sig nzdict { values: Int->Int->(Value-RMS-Zero) }

-- only work with valid matrices of the same size
fact { all m: Matrix | repInv[m] and m.rows = 2 and m.cols = 2 }

-- check that implemented algorithm is correct (it is not)
check implValid {
  all m, m', n', n'': Matrix, boundaries: set Int, mo, io: nzdict {
    (setup[m, boundaries] and
     absBoundary[m, m', boundaries, mo] and
     implBoundary[m, n', n'', boundaries, io]) => 
      (eqMat[m', n''] and eqDict[mo, io] and symmetric[n''])
  }
}

-- check that fixed algorithm is correct (it is)
check fixValid {
  all m, m', n', n'': Matrix, boundaries: set Int, mo, io: nzdict {
    (setup[m, boundaries] and
     absBoundary[m, m', boundaries, mo] and
     fixBoundary[m, n', n'', boundaries, io]) =>
      (eqMat[m', n''] and eqDict[mo, io] and symmetric[n''])
  }
}

/**
ALGORITHMS
*/

-- abstract application of boundaries via documentation
pred absBoundary [m, m': Matrix, boundaries: set Int, obc: nzdict] {
  all i: rowInds[m], j: colInds[m] |
    (i = j and i in boundaries) => m'.values[i][j] = RMS else
    (i in boundaries or j in boundaries) => m'.values[i][j] = Zero else
    m'.values[i][j] = m.values[i][j]
  all i: rowInds[m], j: colInds[m] |
    j in boundaries => {
      (i = j or m.values[i][j] = Zero) => notInDict[obc, i, j] else
      obc.values[i][j] = m.values[i][j]
    } else {
      notInDict[obc, i, j]
    }
  allowIndicesFromMatrix[obc, m]
}

-- implemented algorithm
pred implBoundary [m, m', m'': Matrix, boundaries: set Int, obc: nzdict] {
  -- frame obc
  allowIndicesFromMatrix[obc, m]
  -- first loop (m -> m')
  all b: boundaries |
    m'.values[b][b] = RMS and
    zodRow[m', b]
  all i: rowInds[m]-boundaries |
    unchangedRow[m, m', i]
  -- second loop (m' -> m'')
  all b: boundaries |
    saveNZODcol[m', b, obc] and
    zodCol[m'', b] and
    m''.values[b][b] = m'.values[b][b]
  all j: colInds[m]-boundaries |
    unchangedCol[m', m'', j] and
    colNotInDict[obc, j]
}

-- fixed algorithm
pred fixBoundary [m, m', m'': Matrix, boundaries: set Int, obc: nzdict] {
  -- frame obc
  allowIndicesFromMatrix[obc, m]
  -- first loop (m -> m')
  all b: boundaries |
    saveNZODcol[m, b, obc] and
    zodCol[m', b] and
    m'.values[b][b] = m.values[b][b]
  all j: colInds[m]-boundaries |
    unchangedCol[m, m', j] and
    colNotInDict[obc, j]
  -- second loop (m' -> m'')
  all b: boundaries |
    m''.values[b][b] = RMS and
    zodRow[m'', b]
  all i: rowInds[m]-boundaries |
    unchangedRow[m', m'', i]
}

/**
HELPER PREDICATES
*/

-- RMS not in matrix, force boundary nodes valid, matrix symmetric
pred setup [m: Matrix, boundaries: set Int] {
  RMS not in m.values[univ][univ]
  boundaries in rowInds[m]
  symmetric[m]
}

-- zero off-diagonals in row
pred zodRow [m: Matrix, i: Int] {
  all j: colInds[m] |
    i != j => m.values[i][j] = Zero
}

-- leave row unchanged
pred unchangedRow [m, m': Matrix, i: Int] {
  all j: colInds[m] |
    m'.values[i][j] = m.values[i][j]
}

-- zero off-diagonals in col
pred zodCol [m: Matrix, j: Int] {
  all i: rowInds[m] |
    i != j => m.values[i][j] = Zero
}

-- leave col unchanged
pred unchangedCol [m, m': Matrix, j: Int] {
  all i: rowInds[m] |
    m'.values[i][j] = m.values[i][j]
}

-- save nonzero off-diagonal column values to dict
pred saveNZODcol [m: Matrix, j: Int, d: nzdict] {
  all i: rowInds[m] |
    (i != j and m.values[i][j] != Zero) => 
      d.values[i][j] = m.values[i][j]
    else
      notInDict[d, i, j]
}

-- first->second is not in dictionary
pred notInDict [d: nzdict, first, second: Int] {
  first->second not in d.values.univ
}

-- column index is not in dictionary keys
pred colNotInDict [d: nzdict, j: Int] {
  j not in d.values[univ].univ
}

-- limit indices allowed in dictionary keys
pred allowIndicesFromMatrix [d: nzdict, m: Matrix] {
  all i: d.values.univ.univ |
    0 <= i and i < m.rows
  all j: d.values.univ[univ] |
    0 <= j and j < m.cols
}

-- true if matrix is symmetric
pred symmetric [m: Matrix] {
  repInv[m]
  m.rows = m.cols
  all i: rowInds[m], j: colInds[m] |
    m.values[i][j] = m.values[j][i]
}

-- true if matrices are equivalent
pred eqMat [m, m': Matrix] {
  m.rows = m'.rows
  m.cols = m'.cols
  all i: rowInds[m], j: colInds[m] |
    m.values[i][j] = m'.values[i][j]
}

-- true if dictionaries are equivalent
pred eqDict [d, d': nzdict] {
  d.values = d'.values
}

/**
SIMPLE CASE
*/

pred testmatrix [m: Matrix] {
  some v: Value-RMS-Zero |
    0->0->v in m.values and
    0->1->v in m.values and
    1->0->v in m.values and
    1->1->v in m.values
}

-- abstract
run abs {
  some m, m': Matrix, boundaries: set Int, obc: nzdict {
    boundaries = {0 + 1}
    testmatrix[m]
    absBoundary[m, m', boundaries, obc]
  }
}

-- current implementation
run impl {
  some m, m', m'': Matrix, boundaries: set Int, obc: nzdict {
    boundaries = {0 + 1}
    testmatrix[m]
    implBoundary[m, m', m'', boundaries, obc]
  }
}

-- fixed implementation
run fix {
  some m, m', m'': Matrix, boundaries: set Int, obc: nzdict {
    boundaries = {0 + 1}
    testmatrix[m]
    fixBoundary[m, m', m'', boundaries, obc]
  }
}
