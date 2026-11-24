---- MODULE forall_inf_replay ----
\* Regression for #31: Skolemized \A over infinite set must replay counterexample cleanly.
EXTENDS Naturals
VARIABLE
  \* @type: Int;
  y
Init == y = 5
Next == UNCHANGED y
Inv == \A x \in Nat : x # y
====
INIT Init
NEXT Next
INVARIANT Inv
