---- MODULE enabled_param_prop ----
\* ENABLED of an action parameter is a state predicate in a temporal formula,
\* and WF of an action guarded by (ENABLED B)' becomes disabled once B is
\* disabled in the next state.
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x < 4 /\ x' = x + 1
B == x < 3 /\ x' = x + 1

Prop(A) == [](ENABLED A \/ x = 4)
AlwaysReady == Prop(Next)
Spec == Init /\ [][Next]_x /\ WF_x(Next /\ (ENABLED B)')
Eventually3 == <>(x = 3)
====
SPECIFICATION Spec
PROPERTY AlwaysReady
PROPERTY Eventually3
CHECK_DEADLOCK FALSE
