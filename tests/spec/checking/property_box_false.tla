---- MODULE property_box_false ----
\* []FALSE is checked as an invariant, named FALSE as TLC names it.
VARIABLE s
Init == s = 1
Next == s' = s
Spec == Init /\ [][Next]_s
P == [](FALSE)
====
SPECIFICATION Spec
PROPERTY P
