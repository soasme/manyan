---- MODULE dump_trace_formats ----
\* options: -dumpTrace tla trace.tla -dumpTrace json trace.json
\* Two formats of the counterexample, each written, in the order given.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 2
====
INIT Init
NEXT Next
INVARIANT Inv
