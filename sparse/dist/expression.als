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

pred show {}
run show for 5
