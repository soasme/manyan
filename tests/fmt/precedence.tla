---- MODULE precedence ----
EXTENDS Integers, Sequences
VARIABLE x
Apply(F(_, _)) == F(1, 2)
A == 2 * (-1)
B == -(-1)
C == (SUBSET {1}) \ {{}}
D == [](x = 1)
E == ({1} \X {2}) \X {3}
F == {1} \X {2} \X {3}
G == ("a" \o (IF TRUE THEN "b" ELSE "c")) \o "d"
H == Apply( + ) + Apply( * ) + Apply( - )
I == ~(1 = 2)
J == (1 + 2) - 3
K == 1 - (2 + 3)
L == (TRUE /\ FALSE) \/ TRUE
M == [x' = x]_(<<x>>)
---- MODULE Sub ----
a !! b == <<a, b>>
====
S == INSTANCE Sub
N == S ! !!(1, 2)
====
