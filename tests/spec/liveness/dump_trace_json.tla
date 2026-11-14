---- MODULE dump_trace_json ----
\* -dumpTrace json writes a temporal property's counterexample, its lasso
\* closed by the action back to the state the cycle starts at.
\* options: -dumpTrace json lasso.json
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Live == <>(x = 5)
====
SPECIFICATION Spec
PROPERTY Live
