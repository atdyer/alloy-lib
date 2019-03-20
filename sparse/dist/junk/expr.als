module expr

sig Value {}
lone sig Zero extends Value {}

sig SumProd extends Value {
  values: seq {Value-SumProd} -> {Value-SumProd}
}

fun filterZeros [e: SumProd]: Int {
  e.values.univ.univ - (e.values.univ.Zero + e.values.Zero.univ)
}

pred show {
  one SumProd
}

run show for 4
