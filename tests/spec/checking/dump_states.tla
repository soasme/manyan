---- MODULE dump_states ----
\* options: -deadlock -dump states
\* The states found, in states.dump, as a trace prints them, numbered in
\* the order found; one the constraint leaves out is not among them.
EXTENDS Naturals
VARIABLE x, y
Init == x \in {2, 0} /\ y = "a"
Next == x' \in {x + 1, x + 3} /\ x < 5 /\ y' = y
Con == x < 6
====
INIT Init
NEXT Next
CONSTRAINT Con
