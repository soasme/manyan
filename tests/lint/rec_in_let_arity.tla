---- MODULE rec_in_let_arity ----
A == LET RECURSIVE F(_) F(x, y) == x IN F(1, 2)
====
