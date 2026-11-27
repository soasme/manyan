---- MODULE error_next_replay_fingerprint_continue ----
\* options: -continue
\* Next fails on x = 0; ENABLED B there has a successor TLC cannot
\* fingerprint: with -continue, after the deadlock, it prints the behavior
\* to it as it replays the error, and the error again.
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
