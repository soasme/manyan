---- MODULE dump_trace_deadlock_initial ----
\* A deadlock in the initial state the simulator goes on from, with
\* -continue: its CounterExample is empty, and -dumpTrace writes nothing.
\* options: -simulate num=1 -depth 2 -seed 681 -continue -dumpTrace json trace.json
VARIABLE x
Init == x = 0
Next == x' = 1 /\ x' = 0
====
INIT Init
NEXT Next
