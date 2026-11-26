---- MODULE error_next_replay ----
\* Next fails on x = 0, and so does P's predicate there: TLC reports the
\* error in Next, but as it replays it meets P's first, an exception.
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = CHOOSE v \in {1} : v > x + 5
Spec == Init /\ [][Next]_x
P == <>[](x \in 1)
====
SPECIFICATION Spec
PROPERTY P
