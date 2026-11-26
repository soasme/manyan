---- MODULE subscript_keywords ----
\* Action and fairness subscripts may be TRUE, FALSE, BOOLEAN or STRING.
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x /\ WF_FALSE(Next) /\ SF_TRUE(Next)
Q == [][Next]_FALSE
P == [][Next]_BOOLEAN /\ [][Next]_TRUE /\ WF_STRING(Next)
Inv == ~ENABLED <<Next>>_STRING /\ ~ENABLED <<Next>>_BOOLEAN
====
SPECIFICATION Spec
INVARIANT Inv
PROPERTY P Q
