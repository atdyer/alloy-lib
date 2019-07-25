open csr
open csrRefinement
open matrixTranspose
open util/integer

pred transpose [c, c': CSR] {
  c.rows = c'.cols
  c.cols = c'.rows
  some iao, iao', iao'', iao''': seq Int {
    countcols[c, iao]
    setptrs[iao, iao']
    copyvals[c, c', iao', iao'']
    shift[iao'', iao''']
    c'.IA = iao'''
    #c'.JA = c'.IA.last
    #c'.A = c'.IA.last
  }
}

-- (1)
pred countcols [c: CSR, iao: seq Int] {
  #iao = #c.IA
  iao[0] = 0
  all j: range[c.cols] | iao[j.add[1]] = #c.JA.j
}

-- (2)
pred setptrs [iao, iao': seq Int] {
  #iao = #iao'
  iao'[0] = 0
  all i: iao.butlast.inds |
    let i' = i.add[1] |
      iao'[i'] = iao'[i].add[iao[i']]
}

-- (3)
pred copyvals [c, c': CSR, iao, iao': seq Int] {
  #iao' = #iao
  some ia: Int->Int->Int {
    -- init ia and array lengths
    0->iao in ia
    #ia.Int.Int = add[#c.A, 1]
    all i: ia.Int.Int | #ia[i] = #iao
    -- iterate
    all i: range[c.rows] {
      all k: range[c.IA[i], c.IA[i.add[1]]] {
        let t = k, t' = t.add[1],
            j = c.JA[k], nxt = ia[t][j] {
          ia[t'] = ia[t] ++ j->nxt.add[1]
          c'.JA[nxt] = i
          c'.A[nxt] = c.A[k]
        }
      }
    }
    iao' = ia[c.IA.last]
  }
}

-- (4)
pred shift [iao, iao': seq Int] {
  #iao = #iao'
  iao'[0] = 0
  all i: range[1, #iao] | iao'[i] = iao[i.sub[1]]
}

pred example [c: CSR] {
  repInv[c]
  c.rows = 3
  c.cols = 3
  #c.A = 4
  #c.A[Int] = 4
  c.JA = { 0->1 ++ 1->0 ++ 2->2 ++ 3->1 }
  c.IA = { 0->0 ++ 1->1 ++ 2->3 ++ 3->4 }
}

run {
  some c, c': CSR |
    example[c] and transpose[c, c']
} for 7 seq, 5 Value, 0 Matrix, 2 CSR

check {
  all c, c': CSR, m, m': Matrix |
    example[c] and
    alpha[c, m] and
    transpose[c, c'] and  
    transpose[m, m'] 
      => alpha[c', m']
} for 7 seq, 5 Value, exactly 2 Matrix, exactly 2 CSR

check {
  all c, c': CSR, m, m': Matrix |
    repInv[c] and
    alpha[c, m] and
    transpose[c, c'] and
    transpose[m, m']
      => alpha[c', m']
} for 7 seq, 5 Value, exactly 2 Matrix, exactly 2 CSR
