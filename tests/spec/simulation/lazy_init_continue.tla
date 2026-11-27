---- MODULE lazy_init_continue ----
\* options: -generate num=3 -depth 23 -seed 7 -continue
\* A function kept lazy in an initial state, computed as a behavior checks
\* it: the behaviors after it, with -continue, see it whole (it was kept in
\* the behavior's memory, freed as the next began).
EXTENDS TLC
CONSTANT M
VARIABLES m, f
Init == m \in M /\ f = [s \in SUBSET M |-> m \in s]
Next == m' \in M /\ UNCHANGED f
Inv == f[{m}] = TRUE
====
CONSTANT M = {m1, m2}
INIT Init
NEXT Next
INVARIANT Inv
