---- MODULE set_enum_in_expr ----
\* Regression for #37: {a \in S, TRUE} must parse as a set enumeration, not fail in parse_bounds.
VARIABLE x
Op(a, S) == {a \in S, TRUE}
Init == x = Op(1, {1, 2})
Next == x' = x
====
INIT Init
NEXT Next
