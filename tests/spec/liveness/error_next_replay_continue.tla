---- MODULE error_next_replay_continue ----
\* options: -continue
\* Next fails on x = 0, and so does P's predicate there: TLC reports the
\* error in Next; as it replays it, P's first, then the error in Next again.
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = CHOOSE v \in {1} : v > x + 5
Spec == Init /\ [][Next]_x
P == <>[](x \in 1)
====
SPECIFICATION Spec
PROPERTY P
