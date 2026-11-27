---- MODULE nested_arity ----
\* An error in a nested module: located, as SANY, in the module of the
\* file, from the tokens of the file (a nested module had none: a crash).
---- MODULE Inner ----
F(a) == a
x == F(1, 2)
====
====
