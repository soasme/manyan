---- MODULE ho_param_level ----
VARIABLE x
Prime(a) == a'
Apply(Op(_)) == Op(x')
Bad == Apply(Prime)
====
