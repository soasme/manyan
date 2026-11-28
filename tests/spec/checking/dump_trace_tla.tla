---- MODULE dump_trace_tla ----
\* options: -dumpTrace tla trace.tla
\* The counterexample to a violated invariant as a module of its own,
\* named after its file, defining CounterExample.
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = "a"
Next == x < 3 /\ x' = x + 1 /\ y' = y
Inv == x < 2
====
INIT Init
NEXT Next
INVARIANT Inv
