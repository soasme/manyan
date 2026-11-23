---- MODULE ho_valid ----
EXTENDS Naturals
Apply1(F(_)) == F(TRUE)
Apply2(F(_, _)) == F(1, 2)
A == Apply1(~)
B == Apply2( + )
C == Apply2(LAMBDA x, y : x + y)
====
