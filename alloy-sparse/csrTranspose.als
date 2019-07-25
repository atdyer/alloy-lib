open csr
open csrRefinement
open matrixTranspose
open util/ordering[LS] as ls

-- Loop state for step 3 of algorithm
sig LS {
  i, k: Int,
  ia, ja: seq Int,
  a: seq Value
}

-- count number of values in each column
-- compute IA based on number of values in each column
-- copy values
-- shift iao

pred csrTranspose [c, c': CSR] {
  c.rows = c'.cols
  c.cols = c'.rows
  -- four steps in algorithm
  some iao, iao', iao'', iao''': seq Int {
    countcols[c, iao]
    setptrs[iao, iao']
    copyvals[c, c', iao', iao'']
    shift[iao'', iao''']
    c'.IA = iao'''
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
  initIt[c, iao]
  -- structure
  all it: LS-ls/last {
    it.next.k = it.k.add[1]
    it.k = c.IA[it.i.add[1]].sub[1] => 
      it.next.i = it.i.add[1]
    else
      it.next.i = it.i
  }
  -- values
  all it: LS-ls/last {
    let j = c.JA[it.k], nxt = it.ia[j] {
      it.next.ia = it.ia ++ j->nxt.add[1]
      it.next.ja = it.ja ++ nxt->it.i
      it.next.a = it.a ++ nxt->c.A[it.k]
    }
  }
  iao' = ls/last.ia
  c'.A = ls/last.a
  c'.JA = ls/last.ja
}

-- (4)
pred shift [iao, iao': seq Int] {
  #iao = #iao'
  iao'[0] = 0
  all i: range[1, #iao] | iao'[i] = iao[i.sub[1]]
}

pred initIt [c: CSR, iao: seq Int] {
  ls/first.i = 0
  ls/first.k = 0
  ls/first.ia = iao
  ls/first.ja[Int] = 0
  ls/first.a[Int] = Zero
  #ls/first.ja = #c.JA
  #ls/first.a = #c.A
  #LS = #c.IA.add[1]
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

pred square [c: CSR] {
  c.rows = c.cols
}

run { 
  some c, c': CSR |
    example[c] and
    csrTranspose[c, c']
} for 7 seq, exactly 5 Value, exactly 2 CSR, 0 Matrix, 5 LS

check {
  all c, c': CSR, m, m': Matrix |
    example[c] and
    alpha[c, m] and
    csrTranspose[c, c'] and  
    transpose[m, m'] 
      => alpha[c', m']
} for 7 seq, exactly 5 Value, exactly 2 Matrix, exactly 2 CSR, 5 LS


---
--- work-in-progress, for generalizing check
---

check {
  all c, c': CSR, m, m': Matrix |
    repInv[c] and #c.IA = 4 and square[c] and
    alpha[c, m] and
    csrTranspose[c, c'] and
    transpose[m, m']
      => alpha[c', m']
} for 7 seq, 5 Value, exactly 2 Matrix, exactly 2 CSR, 5 LS


---
--- work-in-progress, for lining up indices and updates
---

pred copyvals2 [c: CSR, iao, iao': seq Int] {
  ls/first.i = -1
  ls/first.k = -1
  ls/first.ia = iao
  -- structure
  all it: LS-ls/last {
    it.next.k = it.k.add[1]
    it.k = c.IA[it.i.add[1]].sub[1] =>
      it.next.i = it.i.add[1]
    else
      it.next.i = it.i
  }
  --values
  all it: LS-ls/first {
    let j = c.JA[it.k], nxt = it.ia[j] {
      it.prev.ia = it.ia ++ j->nxt.sub[1]
    }
  }
}
