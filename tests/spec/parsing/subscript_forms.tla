---- MODULE subscript_forms ----
\* A subscript may be a record, a set or a function, as SANY parses it.
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = 1 /\ UNCHANGED y
Spec == Init /\ [][Next]_<<x, y>> /\ WF_{x, y}(Next) /\ SF_[i \in {1} |-> x](Next)
P == [][Next]_[a |-> x, b |-> y] /\ <>ENABLED <<Next>>_{x}
====
SPECIFICATION Spec
PROPERTY P
