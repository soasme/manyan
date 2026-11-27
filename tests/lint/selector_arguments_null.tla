---- MODULE selector_arguments_null ----
\* Where an operator is, !(e) has no arguments: SANY's error at them.
F(a) == \A b : a = b
G(Op(_, _)) == Op(1, 2)
P == G(F!(1))
====
