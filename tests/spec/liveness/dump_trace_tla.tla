---- MODULE dump_trace_tla ----
\* options: -dumpTrace tla trace.tla
\* A temporal property's counterexample, its lasso, as a module.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
Live == <>(x = 5)
====
SPECIFICATION Spec
PROPERTY Live
