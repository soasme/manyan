---- MODULE union_lazy_fcn ----
\* Set union with an unrealized V_LAMBDA function element must classify it
\* as a function rather than aborting in cup_error.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x
Inv ==
    /\ (CHOOSE f \in {[b \in {TRUE} |-> [r \in {1, 2} |-> 0]][TRUE]} \cup {<<0>>} : f = <<0>>)[x + 1] = 0
    /\ (CHOOSE f \in {[b \in {TRUE} |-> [r \in {1, 2} |-> 0]][TRUE]} \cup {<<0>>} : FALSE)[x] = 0
====
SPECIFICATION Spec
INVARIANT Inv
