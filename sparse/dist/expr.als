module expr

sig Value {}
lone sig Zero extends Value {}

sig Expression extends Value {
  values: seq {Value-Expression} -> {Value-Expression}
}

pred show {
  one Expression
}

run show for 4
