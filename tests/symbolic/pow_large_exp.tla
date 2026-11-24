---- MODULE pow_large_exp ----
\* Regression for #21: symbolic exponentiation uses binary exponentiation, not linear loop.
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x \in {0, 1}
Next == x' = x
Inv == x ^ 1000000 >= 0
====
INIT Init
NEXT Next
INVARIANT Inv
