---- MODULE error_next_replay_fingerprint ----
\* Next fails on x = 0; ENABLED B there has a successor TLC cannot
\* fingerprint, which it does not meet as it replays the error.
EXTENDS Integers
VARIABLE x
Init == x = 0
B == x' = <<>>[1]
Next == x' = CHOOSE v \in {1} : v > x + 5
Spec == Init /\ [][Next]_x
P == []<>(ENABLED B)
====
SPECIFICATION Spec
PROPERTY P
