---- MODULE range_oob_refused ----
\* Regression for #14: huge symbolic range must be refused cleanly, not truncate 64->32 bits.
EXTENDS Integers, FiniteSets
VARIABLE
  \* @type: Bool;
  b
Init == b \in BOOLEAN
Next == b' = b
Inv == Cardinality(((0 - 1000000000) * 3)..(IF b THEN 0 ELSE 1)) >= 0
====
INIT Init
NEXT Next
INVARIANT Inv
