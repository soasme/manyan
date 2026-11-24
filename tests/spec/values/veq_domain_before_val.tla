---- MODULE veq_domain_before_val ----
\* Regression for #35: record/function equality checks all domain keys before comparing values.
VARIABLE x
Init == x = ([a |-> 1, b |-> 2] = [a |-> "x", c |-> 2])
Next == UNCHANGED x
Inv == /\ x = FALSE
       /\ ~([k \in {1, 2} |-> IF k = 1 THEN 1 ELSE 2] = [k \in {1, 3} |-> IF k = 1 THEN "x" ELSE 2])
====
INIT Init
NEXT Next
INVARIANT Inv
