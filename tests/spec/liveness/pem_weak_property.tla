---- MODULE pem_weak_property ----
\* WF_s(A) as a property: TLC checks its negation, <>[]ENABLED and <>[]~A,
\* without a tableau, by the edges that keep both.
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
