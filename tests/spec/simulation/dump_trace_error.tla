---- MODULE dump_trace_error ----
\* An error stops TLC's simulator, -continue or not, the behavior to it
\* its postconditions' CounterExample: -dumpTrace writes it.
\* options: -simulate num=2 -depth 5 -seed 7 -continue -dumpTrace json trace.json
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = CASE x < 2 -> x + 1
====
INIT Init
NEXT Next
