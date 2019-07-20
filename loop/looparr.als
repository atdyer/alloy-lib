open util/ordering[LS] as ls

/**
A = [0 0 0]
for i in range(3):
  A[i] = i
*/

sig LS {
  i: Int,
  arr: seq Int
}

fact {
  ls/first.i = -1
  all s: LS-ls/last |
    s.next.i = s.i.add[1]
}

pred init_array [a: seq Int] {
  #a = 3
  a[Int] = 0
}

pred loop_over_array [a, a': seq Int] {
  #LS = 4
  #a = #a'
  ls/first.arr = a
  all it: LS-ls/first |
    it.arr = it.prev.arr ++ it.i->it.i
  a' = ls/last.arr
}

run {
  some A, A': seq Int |
    init_array[A] and loop_over_array[A, A']
} for 4
