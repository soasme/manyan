---- MODULE dump_trace_implied_init ----
\* A property's state predicate an initial state violates stops TLC, with
\* -continue too, and its CounterExample is the state: -dumpTrace writes it.
\* options: -continue -dumpTrace tla trace.tla
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 1}
Next == x' = 1 - x
P == x \in {0, 1} /\ [](x < 2) /\ x = 1
====
INIT Init
NEXT Next
PROPERTY P
