---- MODULE lambda_wrong_arity ----
Apply(F(_)) == F(1)
A == Apply(LAMBDA x, y : x)
====
