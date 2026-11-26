---- MODULE back_into_root ----
\* semantics: TLC prints the cycle 4 -> 3 -> 1 -> 4 as stuttering in 4, which WF_s(A) rules out
\* The lasso's cycle passes other states and comes back into the state it
\* starts in: it goes back to that state, though TLC prints it stuttering.
EXTENDS Naturals
VARIABLE s
Init == s \in {2, 5}
Next == s' \in <<{1, 4}, {4}, {1, 5}, {1, 3, 4}, {}>>[s]
A == s' \in <<{1, 4}, {}, {1}, {3}, {}>>[s]
Spec == Init /\ [][Next]_s /\ WF_s(A)
P == (TRUE ~> (s \in {1, 4})) ~> FALSE
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
