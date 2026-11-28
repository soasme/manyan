---- MODULE dump_cut_continue ----
\* With -continue TLC stops its temporal checks at a finite counterexample
\* with an exception, and expands the state again to report it: -dump dot
\* writes its steps once more.
\* options: -continue -dump dot states
VARIABLE s
Succ == <<{1, 2}, {3}, {3}>>
Init == s = 1
Next == s' \in Succ[s]
Spec == Init /\ [][Next]_s
P == (FALSE /\ [](s = 1)) \/ (s = 2)
====
SPECIFICATION Spec
PROPERTY P
