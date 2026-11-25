---- MODULE message_cascade ----
\* Formatting a function-domain error must not cascade error formatting inside
\* try_realize() when nested lazy functions fail.
\* options: -deadlock
EXTENDS Naturals
VARIABLE x
RECURSIVE G(_)
G(k) == IF k = 0 THEN [s \in {1} |-> 0][2]
        ELSE [s \in {1, 2, 3} |-> [t \in {1} |-> G(k - 1)]][4]
Init == x = 0
Next == x' = G(6)
Spec == Init /\ [][Next]_x
====
SPECIFICATION Spec
