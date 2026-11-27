---- MODULE prefix_postfix ----
\* A postfix operator on the operand of ENABLED, UNCHANGED, [] or <> keeps
\* its parentheses, which SANY needs; '(e) is e'.
VARIABLE x
a ^+ == a
P == ENABLED (x') /\ ENABLED '(x = 1) /\ UNCHANGED (x^+)
Q == [] ((x = 1)^+) /\ <>^+(x = 1)
====
