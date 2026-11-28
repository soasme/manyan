---- MODULE dump_trace_continue_initial ----
\* With -continue, initial states that violate an invariant leave TLC's
\* CounterExample empty: -dumpTrace writes nothing.
\* options: -continue -dumpTrace json trace.json
EXTENDS Naturals
VARIABLE x
Init == x \in 1..5
Next == UNCHANGED x
Small == x < 4
====
INIT Init
NEXT Next
INVARIANT Small
