---- MODULE invariant_strong_fairness ----
\* TLC evaluates SF_x(B)'s ENABLED on the states expanded before it
\* reports a violated invariant: the successor it reports is kept.
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = <<>>
A == x' = Append(x, 1)
B == Len(x) > 5 /\ x' = <<>>
Spec == Init /\ [][A \/ B]_x /\ SF_x(B)
Inv == Len(x) < 2
P == []<>(x = <<>>)
====
SPECIFICATION Spec
INVARIANT Inv
PROPERTY P
