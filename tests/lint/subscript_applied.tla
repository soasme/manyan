---- MODULE subscript_applied ----
\* As SANY, the arguments of a subscript's last name are dropped:
\* [A]_F(x) is [A]_F, F applied to none.
VARIABLE x
F(a) == a
P == [][x' = x]_F(x)
====
