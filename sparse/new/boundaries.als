open matrix
open matrixAnalysis

-- - start with a matrix
-- - create a 'boundary applied' equivalent that matches
--   the description in docs
-- - model the algorithm and see if it does the same thing

/*
From ADCIRC documentation:
- on-diagonal term equal to RMS of all diagonals
- zero all off-diagonal terms in the row
- zero all off-diagonal terms in column
*/

sig RMS extends Value {}

sig OBCCOEF {
  values: Int->Int->(Value-RMS)
}

-- abstract version via documentation
pred absBoundary [m, m': Matrix, nodes: set Int, obc: OBCCOEF] {
  all i: rowInds[m], j: colInds[m] |
    (i=j) => m'.values[i][j] = RMS else
    (i in nodes or j in nodes) => m'.values[i][j] = Zero else
    m'.values[i][j] = m.values[i][j]
  -- save off-diagonal nonzero terms in each boundary node column
  all b: nodes |
    all r: rowInds[m] |
      (b=r) => r->b not in obc.values.univ else
      (m.values[r][b] != Zero) => obc.values[r][b] = m.values[r][b] else
      (m.values[r][b] = Zero) => r->b not in obc.values.univ
  all i: obc.values.univ.univ |
    0 <= i and i < m.rows
  all j: obc.values.univ[univ] |
    0 <= j and j < m.cols
}

-- implemented version via fortran
pred implBoundary [m, m', m'': Matrix, nodes: set Int, obc: OBCCOEF] {

}

pred fixBoundary [m, m', m'': Matrix, nodes: set Int, obc: OBCCOEF] {

}

pred zeroRowSetRMS [m, m': Matrix, nodes: set Int] {
  all i: rowInds[m], j: colInds[m] |
    i in nodes => {
      i=j => m'.values[i][j] = RMS else m'.values[i][j] = Zero
    } else {
      m'.values[i][j] = m.values[i][j]
    }
}

pred zeroColSaveNZ [m, m': Matrix, boundaries: set Int, obc: OBCCOEF] {
  all i: rowInds[m], j: colInds[m] |
    j in boundaries => {
      i != j => {
        m'.values[i][j] = Zero
        m.values[i][j] != Zero => obc.values[i][j] = m.values[i][j] else i->j not in obc.values.univ
      }
    } else {
    }
}

pred symmetric [m: Matrix] {
  repInv[m]
  m.rows = m.cols
  all i: rowInds[m], j: colInds[m] |
    m.values[i][j] = m.values[j][i]
}

pred setup [m, m': Matrix] {
  repInv[m]
  repInv[m']
  symmetric[m]
  RMS not in m.values[univ][univ]
  m.rows = m'.rows
  m.cols = m'.cols
  hasNonzeroValues[m]
}

pred hasNonzeroValues [m: Matrix] {
  some i: rowInds[m], j: colInds[m] |
    i != j and
    m.values[i][j] != Zero
}

pred showAbs {
  some m, m': Matrix, nodes: set rowInds[m], obc: OBCCOEF |
    #nodes > 1 and
    setup[m, m'] and
    absBoundary[m, m', nodes, obc] and
    disj[m, m'] and
    m.rows = 2
}

run showAbs
