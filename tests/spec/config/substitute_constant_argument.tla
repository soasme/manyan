---- MODULE substitute_constant_argument ----
\* An operator substituted by a constant, given as an operator argument:
\* a value applied is the value.
EXTENDS Naturals
CONSTANT C
F(a, b) == a + b
Apply(Op(_, _), a, b) == Op(a, b)
VARIABLE x
Init == x = Apply(F, 1, 2)
Next == x' = x
Inv == x = 3
====
CONSTANT
  C = 5
  F <- C
INIT Init
NEXT Next
INVARIANT Inv
