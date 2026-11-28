---- MODULE dump_dot_no_init ----
\* No initial predicate, so no states: TLC closes the graph it began.
\* options: -dump dot states
Init == TRUE
Next == TRUE
Spec == Init /\ [][Next]_<<>>
Inv == 1 + 1 = 2
====
SPECIFICATION Spec
INVARIANT Inv
