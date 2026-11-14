---- MODULE reprint_tableau_view ----
\* As etcd's trace validation: a VIEW, and TLCGet("queue") in a temporal
\* property, each atom as TLC evaluates it in the state it expands then.
EXTENDS Naturals, TLC
VARIABLE l, x
Init == l = 1 /\ x = 0
Next == l < 4 /\ l' = l + 1 /\ x' = x /\ PrintT(<<"step", l>>)
Spec == Init /\ [][Next]_<<l, x>>
View == <<x, l>>
Matched == [](l <= 3 => [](TLCGet("queue") = 1 \/ l > 3))
====
SPECIFICATION Spec
VIEW View
PROPERTY Matched
CHECK_DEADLOCK FALSE
