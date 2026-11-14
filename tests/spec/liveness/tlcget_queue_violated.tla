---- MODULE tlcget_queue_violated ----
\* A state with two successors leaves two on the queue.
EXTENDS Naturals, TLC
VARIABLE l
Init == l = 1
Next == l < 3 /\ l' \in {l + 1, l + 10}
Spec == Init /\ [][Next]_l
Matched == [](l < 3 => [](TLCGet("queue") = 1 \/ l >= 3))
====
SPECIFICATION Spec
PROPERTY Matched
