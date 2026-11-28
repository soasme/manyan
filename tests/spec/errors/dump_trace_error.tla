---- MODULE dump_trace_error ----
\* An error evaluating Next is no counterexample: TLC rebuilds the behavior
\* for its postconditions, but -dumpTrace writes nothing.
\* options: -dumpTrace tla trace.tla
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x < 2 /\ Assert(x < 1, "too far") /\ x' = x + 1
====
INIT Init
NEXT Next
