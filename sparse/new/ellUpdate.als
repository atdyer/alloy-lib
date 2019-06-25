open ell

pred updateELL [e, e': ELL, row, col: Int, val: Value] {
  e'.rows = e.rows
  e'.cols = e.cols
  e'.maxnz = e.maxnz
  rowInRange[e, row]
  colInRange[e, col]
  NZtoNZ[e, e', row, col, val] or
  NZtoZ[e, e', row, col, val] or
  ZtoNZ[e, e', row, col, val] or
  ZtoZ[e, e', row, col, val]
}

pred NZtoNZ [e, e': ELL, row, col: Int, val: Value] {
  get[e, row, col] != Zero
  val != Zero
  e'.columns = e.columns
  let a = mul[row, e.maxnz],                 -- row start index
      b = add[a, e.maxnz],                   -- row end index
      sc = e.columns.subseq[a, sub[b, 1]],   -- row columns
      i = add[a, sc.idxOf[col]] {            -- index of col in e.columns
    e'.values = e.values.setAt[i, val]
  }
}

pred NZtoZ [e, e': ELL, row, col: Int, val: Value] {
  get[e, row, col] != Zero
  val = Zero
  let a = mul[row, e.maxnz],
      sc = rowcols[e, row],
      i = add[a, sc.idxOf[col]] {
    e'.columns = e.columns.setAt[i, -1]
    e'.values = e.values.setAt[i, Zero]
  }
}

pred ZtoNZ [e, e': ELL, row, col: Int, val: Value] {
  get[e, row, col] = Zero
  val != Zero
  let a = mul[row, e.maxnz],
      sc = rowcols[e, row],
      i = sc.idxOf[-1] {
    some i
    e'.columns = e.columns.setAt[add[a, i], col]
    e'.values = e.values.setAt[add[a, i], val]
  }
}

pred ZtoZ [e, e': ELL, row, col: Int, val: Value] {
  get[e, row, col] = Zero
  val = Zero
  e'.values = e.values
  e'.columns = e.columns
}
