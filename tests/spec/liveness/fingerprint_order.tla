---- MODULE fingerprint_order ----
\* TLC's counterexample follows its order of a state's successors, by
\* their fingerprints under the -fp polynomial.
\* options: -fp 9
VARIABLE s
Succ == <<{3, 5}, {1, 2, 3}, {1, 3, 4}, {2, 3, 4}, {2, 4, 5}>>
Init == s \in {1, 2, 3, 4, 5}
Next == s' \in Succ[s]
Spec == Init /\ [][Next]_s
P == <>[][s' \in {1, 3, 5}]_s
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
