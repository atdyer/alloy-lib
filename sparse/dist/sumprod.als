/**
The SumProd signature represent a sum of products, for
example: 0*1 + 2*3 + 4*5. Because this type of expression
evaluates to a single value, the SumProd signature is
an extension of the Value signature.

SumProd is made to be used in matrix-vector multiplication,
where the resultant vector contains a sum of products for
each row. Helper funs/preds that deal with the presence of
zeros if SumProds are provided to assist with the analysis
of sparse matrix-vector multiplications.
**/

open value

sig SumProd extends Value {
  values: seq {Value-SumProd} -> {Value-SumProd}
}

fun filterZeros [e: SumProd]: Int {
  e.values.univ.univ - (e.values.univ.Zero + e.values.Zero.univ)
}

pred isZero [e: SumProd] {
  no filterZeros[e]
}

