---- MODULE inf_range_empty_eq ----
\* Regression for #28: empty symbolic ranges must compare equal, not by endpoints.
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x \in {2, 3}
Next == UNCHANGED x
Inv == (x..1) = ((x + 1)..1)
====
INIT Init
NEXT Next
INVARIANT Inv
