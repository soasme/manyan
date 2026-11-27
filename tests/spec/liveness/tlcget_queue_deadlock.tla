---- MODULE tlcget_queue_deadlock ----
\* options: -deadlock
\* Without the deadlock, TLC's counts are still those as it stopped.
\* TLCGet's counts in a temporal property are TLC's as it adds a state to
\* its temporal checks, once it has generated the successors of the state
\* before: etcd's trace validation checks the queue holds one state. Under
\* [] only, TLC checks a state predicate as an invariant instead.
EXTENDS Naturals, TLC
VARIABLE l
Init == l = 1
Next == l < 5 /\ l' = l + 1
Spec == Init /\ [][Next]_l
Matched == [](l < 5 => [](TLCGet("queue") = 1 \/ l >= 5))
Found == [](l > 0 => [](TLCGet("distinct") = l))
====
SPECIFICATION Spec
PROPERTY Matched
PROPERTY Found
