---- MODULE always_wf ----
\* []WF_v(A) simplifies to WF_v(A) because WF_v(A) is []<>(~ENABLED <<A>>_v \/ <<A>>_v).
\* options: -deadlock
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P1 == []WF_x(FALSE)
P2 == []WF_x(x = 5)
P3 == []WF_x(Next)
====
SPECIFICATION Spec
PROPERTY P1
PROPERTY P2
PROPERTY P3
