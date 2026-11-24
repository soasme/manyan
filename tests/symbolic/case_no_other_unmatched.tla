---- MODULE case_no_other_unmatched ----
\* Regression for #30: CASE without OTHER must not drop last arm's guard.
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x = 2
Next == UNCHANGED x
Inv == CASE x = 1 -> TRUE
====
INIT Init
NEXT Next
INVARIANT Inv
