---- MODULE trace_domain ----
\* The domain of a state of Trace is the set of its variables' names.
EXTENDS Naturals, TLC, TLCExt
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y
Small == x < 2
Inv == x = 0 \/ PrintT(DOMAIN Trace[1])
====
INIT Init
NEXT Next
INVARIANT Inv
CONSTRAINT Small
