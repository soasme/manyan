---- MODULE ho_prime_outer ----
VARIABLE x
Id(a) == a
Apply(Op(_), v) == Op(v)'
Bad == Apply(Id, x')
====
