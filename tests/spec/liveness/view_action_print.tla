---- MODULE view_action_print ----
\* Under a VIEW an action of a temporal property is evaluated on the
\* successors themselves, which TLC generated once: Next prints once.
EXTENDS Naturals, TLC
VARIABLE x, n
Init == x = 0 /\ n = 0
Next == x' = (x + 1) % 3 /\ n' = (n + 1) % 2 /\ PrintT(<<"step", x>>)
Spec == Init /\ [][Next]_<<x, n>>
Steps == [][x' = (x + 1) % 3]_x
View == x
====
SPECIFICATION Spec
PROPERTY Steps
VIEW View
