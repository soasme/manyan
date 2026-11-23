---- MODULE ho_wrong_arity ----
Apply(F(_)) == F(1)
G(x, y) == x
A == Apply(G)
====
