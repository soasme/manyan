---- MODULE stuttering_warning_error_model ----
\* options: -fp 13
\* The negation's disjunct []TRUE, an error model without cycle conditions,
\* finds the stuttering counterexample: TLC warns of fairness only where
\* the error model that found it has conditions, not another one.
EXTENDS Naturals
VARIABLE s
Succ == <<{1, 2}, {2}, {}>>
Init == s \in {1, 3}
Next == s' \in Succ[s]
Spec == Init /\ [][Next]_<<s>>
P == ~[](TRUE \/ s \in {2, 3}) /\ (TRUE ~> (s \in {1} ~> ~(s \in {2})))
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
