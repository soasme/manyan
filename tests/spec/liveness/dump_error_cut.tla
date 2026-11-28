---- MODULE dump_error_cut ----
\* An error in TLC's temporal checks stops it where they had come: -dump
\* holds the states it had written until then.
\* options: -dump states
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Spec == Init /\ [][Next]_x
P == []<><<x = 1 /\ x' = "s">>_x
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
