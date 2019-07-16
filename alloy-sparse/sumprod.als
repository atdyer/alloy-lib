open value

sig SumProd {
  vals: Int->lone Value->Value
} {
  all i: vals.univ.univ | i >= 0
}
