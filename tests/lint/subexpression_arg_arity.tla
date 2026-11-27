---- MODULE subexpression_arg_arity ----
\* A part of a definition where an operator is: of the arity wanted.
F(a) == lab :: {a}
G(Op(_, _)) == Op(1, 2)
P == G(F!lab)
====
