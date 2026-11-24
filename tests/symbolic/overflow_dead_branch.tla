---- MODULE overflow_dead_branch ----
\* Regression for #26: no_overflow in untaken IF branch must not prune valid 64-bit counterexamples.
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Big == 1000000000 * 1000000000
Init == x \in Int /\ x > 0
Next == x' = x
Inv == IF x < 10 THEN x * x >= 0 ELSE x <= Big
====
INIT Init
NEXT Next
INVARIANT Inv
