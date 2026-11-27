---- MODULE simulate_pem_action ----
\* WF_s(A) as a property in a simulation: its negation <>[](ENABLED /\ ~A)
\* has no temporal formula under <>[], so TLC checks it without a tableau,
\* on a behavior of one state stuttering.
\* options: -simulate num=1 -depth 18 -seed 33
VARIABLE s
Succ == <<{2, 3}, {}, {3}>>
Init == s \in {1, 2}
Next == s' \in Succ[s]
A0 == s' \in <<{}, {}, {}>>[s]
Spec == Init /\ [][Next]_s /\ WF_s(A0)
P == WF_s(s' \in {1})
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
