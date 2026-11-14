---- MODULE inv_option_order ----
\* An -inv is checked after the configuration's invariants: both fail on
\* the same state, and the configuration's is reported.
\* options: -inv "x < 2"
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 2
====
INIT Init
NEXT Next
INVARIANT Inv
