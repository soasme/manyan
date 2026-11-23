---- MODULE rec_let_wrong_level ----
A == LET RECURSIVE F(_) IN LET F(x) == x IN F(1)
====
