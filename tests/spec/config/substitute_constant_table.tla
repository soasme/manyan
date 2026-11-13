---- MODULE substitute_constant_table ----
\* An operator substituted by a constant without parameters whose value is
\* an operator table: the table is applied to the operator's arguments.
EXTENDS Naturals
CONSTANT C
F(a, b) == a + b
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Inv == F(x, 0) = F(0, 0)
====
CONSTANT
  C(0, 0) = 0
  C(1, 0) = 0
  C(2, 0) = 1
  F <- C
INIT Init
NEXT Next
INVARIANT Inv
