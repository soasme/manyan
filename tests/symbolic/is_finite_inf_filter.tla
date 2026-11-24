---- MODULE is_finite_inf_filter ----
\* Regression for #28: IsFiniteSet on filtered infinite set must not spuriously return TRUE.
EXTENDS FiniteSets, Naturals
VARIABLE
  \* @type: Int;
  x
Init == x = 0
Next == UNCHANGED x
Inv == IsFiniteSet({y \in Nat : y > x})
====
INIT Init
NEXT Next
INVARIANT Inv
