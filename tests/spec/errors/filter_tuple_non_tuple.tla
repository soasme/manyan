---- MODULE filter_tuple_non_tuple ----
\* Regression for #35: tuple-pattern filter {<<u, v>> \in S : P} must reject non-tuple records.
VARIABLE x
Init == x = ([a |-> 1, b |-> 2] \in {<<u, v>> \in [a : {1}, b : {2}] : u = 1})
Next == UNCHANGED x
====
INIT Init
NEXT Next
