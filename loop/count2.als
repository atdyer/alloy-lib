open util/ordering[LS] as ls
open util/relation

-- Loop State (LS)
sig LS {
  i, counter: Int
}

fact {
  ls/first.i = -1
  ls/first.counter = 0
  all s: LS-ls/last |
    s.next.i = s.i.add[1]
}

pred c1 [s: seq Int, count: Int] {
  count = #{ i: dom[s] | rem[s[i], 2] = 0 }
}

pred c2 [s: seq Int, count: Int] {
  #LS = #s.add[1]
  ls/first.counter = 0
  all it: LS-ls/first {
    rem[s[it.i], 2] = 0 =>
      it.counter = it.prev.counter.add[1]
        else it.counter = it.prev.counter
  }
  count = ls/last.counter
}

run {
  some s: seq Int, count: Int | c2[s, count]
}

-- cannot enforce number of LS atoms on right side of implication
assert sameCount12 {
  all s: seq Int, count: Int |
    (#s = 4 and c1[s, count]) => c2[s, count]
}

-- works
assert sameCount21 {
  all s: seq Int, count: Int |
    c2[s, count] => c1[s, count]
}

check sameCount12 for 4 Int, exactly 5 LS
check sameCount21 for 5 Int
