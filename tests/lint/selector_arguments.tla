---- MODULE selector_arguments ----
\* Where an operator is, no selector has arguments: SANY's error at it.
F(a) == \A b : a = b
G(Op(_)) == Op(1)
P == G(F(1)!@)
====
