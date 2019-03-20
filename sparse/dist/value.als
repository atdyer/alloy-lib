/**
The Value signature represents some numerical value.
The Zero signature, an extension of the Value signature,
is meant to represent the value 0 so that all other
Value atoms may be interpreted as non-zero values.
**/

module value

sig Value {}
one sig Zero extends Value {}
