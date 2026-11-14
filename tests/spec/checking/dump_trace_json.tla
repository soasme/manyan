---- MODULE dump_trace_json ----
\* -dumpTrace json FILE writes the counterexample as TLC's JSON: its
\* states and the actions between them, with the variables.
\* options: -dumpTrace json trace.json
EXTENDS Naturals
VARIABLE x, s
Init == x = 0 /\ s = {}
Inc == x' = x + 1 /\ s' = s \cup {x}
Reset == x > 1 /\ x' = 0 /\ UNCHANGED s
Next == Inc \/ Reset
Inv == x < 3
====
INIT Init
NEXT Next
INVARIANT Inv
