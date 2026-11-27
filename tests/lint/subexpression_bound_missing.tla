---- MODULE subexpression_bound_missing ----
\* A part under a bound name, as an expression, takes its value: SANY's
\* error without it.
f[a \in {}] == {a}
P == f!@
====
