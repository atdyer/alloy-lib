module expression

open value
open util/graph[Expression]

-- An Expression is some numerical operator that
-- takes numerical values as inputs and reduces them
-- to a single numerical value
abstract sig Expression extends Value { variables: set Value }
fact { dag[variables] }

-- A Sum represents the summation of all variables
sig Sum extends Expression {} { #variables > 1 }

-- A Product represents the product of all variables
sig Product extends Expression {} { #variables > 1 }


pred sumProdEqv [a, b: Sum] {

  -- both sums are sums of products
  all v: a.variables | v in Product and all w: v.variables | w not in Expression
  all v: b.variables | v in Product and all w: v.variables | w not in Expression

  -- summations are the same after removing all products of zero
  filterZeroProducts[a.variables <: Product] = filterZeroProducts[b.variables <: Product]
}

-- two products do not share any variables
pred disjProducts [a, b: Product] {
  all v: a.variables | v not in b.variables
  all v: b.variables | v not in a.variables
}

pred showSumProd {
  some u, v: Sum | disj[u, v] and sumProdEqv[u, v]
}

run showSumProd for 6


pred test {
  #Sum = 1
  #Product = 2
  some s: Sum | s.variables in Product
  all p: Product | #p.variables = 2 and all v: p.variables | v not in Expression
}

run test for 8





fun filterZeroProducts [x: Product]: Product {
  x - { p: Product | some Zero and Zero in p.variables }
}


fun reduce [x: Sum]: Value {
  #(x.variables - Zero) = 1 => x.variables - Zero else x
}

fun reduce [x: Product]: Value {
  some Zero and Zero in x.variables => Zero else x
}

pred showSum {
  some Sum some Product
}

run showSum for 5




pred sameSum [x, y: Sum] {
  (x = y) or 
  (some Zero and x.variables - Zero = y.variables - Zero)
}



pred eqv [x, y: Value] {
  (x = y) 
}

pred sameValue [x, y: Value] {
  x = y
}

pred notFunction [x, y: Expression] {
  y not in x.^variables and x not in y.^variables
}



pred sameProduct [x, y: Product] {
  (x = y) or (some Zero and Zero in x.variables and Zero in y.variables)
}

pred show {
  some x, y: Product | sameProduct[x, y] and disj[x, y] and notFunction[x, y]
}

run show for 5




