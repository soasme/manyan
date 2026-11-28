---- MODULE dump_trace_unassigned ----
\* A successor that leaves a variable out: TLC's -dumpTrace postcondition,
\* checked first, fails on the behavior, after the simulation's summary.
\* options: -simulate num=4 -depth 19 -seed 262 -continue -dumpTrace tla trace.tla
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 1
Next == x' = x + 1 /\ (x < 2 => y' = y)
====
INIT Init
NEXT Next
