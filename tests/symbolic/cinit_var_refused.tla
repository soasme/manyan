\* options: -cinit CInit
---- MODULE cinit_var_refused ----
\* Regression for #21: -cinit referencing a VARIABLE must be rejected cleanly, not read OOB/type-confuse.
EXTENDS Integers
CONSTANT
  \* @type: Str;
  C
VARIABLE
  \* @type: Int;
  a
CInit == C = "hi" /\ a + 1 = 2
Init == a = 0
Next == a' = a
Inv == a = 0
====
INIT Init
NEXT Next
INVARIANT Inv
