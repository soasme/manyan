---- MODULE inf_filter_eq_refused ----
\* Regression for #28: equality on filtered infinite sets must not spuriously return TRUE.
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x = 2
Next == UNCHANGED x
Inv == {y \in Int : y > x} = {y \in Int : y < x}
====
INIT Init
NEXT Next
INVARIANT Inv
