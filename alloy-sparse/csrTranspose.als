open csr

-- count number of values in each column
-- compute IA based on number of values in each column
-- copy values
-- shift iao

pred csrTranspose [c, c': CSR] {
  some iao, iao': seq Int {
    countcols[c, iao]
    setptrs[iao, iao']
  }
}

pred countcols [c: CSR, iao: seq Int] {
  #iao = #c.IA
  iao[0] = 0
  all j: range[c.cols] | iao[j.add[1]] = #c.JA.j
}

pred setptrs [iao, iao': seq Int] {
  #iao = #iao'
  iao'[0] = 0
  all i: iao.butlast.inds |
    let i' = i.add[1] |
      iao'[i'] = iao'[i].add[iao[i']]
}

//pred copyvals [c, c': CSR, iao: seq Int] {
//  all i: range[c.rows] {
//    all k: range[c.IA[i], c.IA[i.add[1]]] {
//      let j = c.JA[k],
//          next = iao[j] { --      <---\
//        -- c'.A[next] = a[k]          |
//        -- c'.JA[next] = i            |
//        -- iao[j] = next + 1      <---/
//      }
//    }
//  }
//}

pred example [c: CSR] {
  c.rows = 3
  c.cols = 3
  #c.A = 4
  c.JA = { 0->1 ++ 1->0 ++ 2->2 ++ 3->1 }
  c.IA = { 0->0 ++ 1->1 ++ 2->3 ++ 3->4 }
}

run { 
  some c, c': CSR |
    repInv[c] and repInv[c'] and
    example[c] and
    csrTranspose[c, c']
} for 7 seq, exactly 5 Value, exactly 2 CSR, 0 Matrix
