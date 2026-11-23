---- MODULE ho_coparam_level ----
VARIABLE x
Prime(a) == a'
Apply(Op(_), v) == Op(v)
Bad == Apply(Prime, x')
====
