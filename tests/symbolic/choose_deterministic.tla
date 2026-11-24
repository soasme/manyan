---- MODULE choose_deterministic ----
\* Regression for #31: CHOOSE must be deterministic across repeated evaluations and replay cleanly.
EXTENDS Integers
VARIABLES
  \* @type: Set(Int);
  S,
  \* @type: Int;
  y
Pick(T) == CHOOSE z \in T : TRUE
Init == S = {1, 2} /\ y \in {1, 2}
Next == UNCHANGED <<S, y>>
Inv == /\ (CHOOSE z \in S : TRUE) = (CHOOSE z \in S : TRUE)
       /\ Pick({y, y + 1}) = Pick({y, y + 1})
====
INIT Init
NEXT Next
INVARIANT Inv
