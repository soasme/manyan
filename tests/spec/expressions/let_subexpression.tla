---- MODULE let_subexpression ----
\* A subexpression of a LET definition, in the scope of the LET and of
\* what binds around it, as TLC evaluates it.
EXTENDS TLC, Naturals
VARIABLE v
ASSUME PrintT({LET G == <<y, y + 1>> IN G!2 : y \in {1, 2, 3}})
ASSUME PrintT({LET F(x) == x + y IN F(10)!1 : y \in {1, 2}})
ASSUME PrintT(LET F(x) == lab :: {x, 7} IN F(1)!lab!2)
ASSUME PrintT(LET F(x) == x + 2 IN LET G(Op(_)) == Op(5) IN G(F!1))
ASSUME PrintT(LET a == 4 F(x) == <<x, a>> IN F(1)!2)
ASSUME PrintT(\A y \in {1, 2} : LET F(x) == x = y IN F(y)!1 = y)
Init == v = 0
Next == v' = (LET F(x) == x + v IN F(1)!1) % 3
Inv == LET G == v + 1 IN G!1 = v
====
INIT Init
NEXT Next
INVARIANT Inv
