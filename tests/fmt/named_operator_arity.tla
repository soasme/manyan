---- MODULE named_operator_arity ----
\* An operator written as a name with arguments its form does not take:
\* as written, for SANY's semantics to report.
VARIABLE x
A == +(1, 2)
B == +(1, 2, 3)
C == 1 + => (2)
D == '(x, x)
====
