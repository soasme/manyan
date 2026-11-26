---- MODULE tableau_state_negation ----
\* The negation folds to the state predicate s # 2, checked with a
\* tableau as TLC checks it: the search stops at the first state.
VARIABLE s
Succ == <<{1, 2}, {3}, {3}>>
Init == s = 1
Next == s' \in Succ[s]
Spec == Init /\ [][Next]_s
P == (FALSE /\ [](s = 1)) \/ (s = 2)
====
SPECIFICATION Spec
PROPERTY P
