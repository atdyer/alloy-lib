sig LS {
  nxt: one LS
}


run {
  some init: LS, iterations: seq LS {
    iterations[0] = init
    all it: iterations.butlast {
      iterations[iterations.it.add[1]] = it.nxt
    }
  }
}
