---- MODULE invariant_action_except ----
\* Regression for #17: EXCEPT !.field in an action-level INVARIANT.
VARIABLE x
Init == x = [a |-> 0]
Next == x' = x
BadInv == [[a |-> 0] EXCEPT !.a = 1] = x'
====
INIT Init
NEXT Next
INVARIANT BadInv
