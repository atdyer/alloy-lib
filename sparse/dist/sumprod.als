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
  values: Int -> (Value-SumProd) -> (Value-SumProd)
}

fun nonzeroIndices [e: SumProd]: Int {
  e.values.univ.univ - (e.values.univ.Zero + e.values.Zero.univ)
}

fun removeZeros [e: SumProd]: Int->Value->Value {
  nonzeroIndices[e] <: e.values
}

pred isZero [e: SumProd] {
  no removeZeros[e]
}

pred sumProdEqv [x, y: SumProd] {
  removeZeros[x] = removeZeros[y]
}

pred valEqv [x, y: Value] {
  (x = y)
  or (x in SumProd and isZero[x] and y = Zero)
  or (y in SumProd and isZero[y] and x = Zero)
  or (x in SumProd and y in SumProd and all i: Int | x.values[i] = y.values[i])
}

pred showSumProdEqv { some x, y: SumProd | sumProdEqv[x, y] and disj[x, y] }
pred showValEqv { some x, y: Value | valEqv[x, y] }

run showSumProdEqv for 5
run showValEqv for 3
