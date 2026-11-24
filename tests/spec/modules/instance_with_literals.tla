---- MODULE instance_with_literals ----
\* Regression for #37: INSTANCE ... WITH TRUE/FALSE/BOOLEAN/STRING and multi-line expressions.
---- MODULE M ----
CONSTANTS B, R
X == IF B THEN R.a ELSE 0
====
VARIABLE x
I == INSTANCE M WITH
    B <- TRUE,
    R <- [
        a |-> 1
    ]
Init == x = I!X
Next == x' = x
====
INIT Init
NEXT Next
