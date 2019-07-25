open util/ordering[LS] as ls
open util/integer

sig LS {
  i, j: Int
}

pred loop_structure [a: seq Int] {
  ls/first.i = 0
  ls/first.j = a[0]
  all it: LS-ls/last {
    it.j = a[it.i.add[1]].sub[1] => {
      it.next.i = it.i.add[1]
    } else {
      it.next.i = it.i
    }
    it.next.j = it.j.add[1]
  }
}

pred testarray [a: seq Int] {
  #a = 4
  a[0] = 0
  a[1] = 1
  a[2] = 3
  a[3] = 4
}

run {
  some a: seq Int | testarray[a] and loop_structure[a]
} for 4
