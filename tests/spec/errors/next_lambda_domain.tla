---- MODULE next_lambda_domain ----
\* Applying a function constructor outside its domain in Next throws a
\* TLCRuntimeException (exit 75), not an EvalException (exit 255).
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = [r \in {5, 6} |-> 1][7]
Spec == Init /\ [][Next]_x
====
SPECIFICATION Spec
