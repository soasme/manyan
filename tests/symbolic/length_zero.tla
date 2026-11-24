\* options: -length 0
---- MODULE length_zero ----
\* Regression for #15: -length 0 must check only depth 0 (initial states), not 10 steps.
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x = 0
Next == x' = x + 1
Inv == x < 3
====
INIT Init
NEXT Next
INVARIANT Inv
