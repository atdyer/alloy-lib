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

-- Sums are equivalent if they contain the same
-- values when all zeros are removed
pred sumsEqv [a, b: Sum] {
  a.variables - Zero = b.variables - Zero
}

-- Products are equivalent if the contain the
-- same values or both contain a single zero
pred prodEqv [a, b: Product] {
  (a.variables = b.variables) or
  (some Zero and Zero in a.variables and Zero in b.variables)
}

pred show {
--  some a, b: Sum | sumsEqv[a, b] and disj[a, b]
  some a, b: Product | prodEqv[a, b] and disj[a, b]
}
run show for 6


