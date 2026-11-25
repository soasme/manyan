---- MODULE label_later_bound ----
\* A label in a later bound's set is outside the scope of earlier bounds of
\* the same construct, so it must not require them as formal parameters.
EXTENDS Integers
P1 == [a \in {1}, b \in (l1 :: {2}) |-> 1]
P2 == {1 : a \in {1}, b \in (l2 :: {2})}
P3 == \E a \in {1}, b \in (l3 :: {2}) : TRUE
P4 == \A a \in {1}, b \in (l4 :: {2}) : TRUE
P5 == \A x \in {1} : [a \in {1}, b \in (l5(x) :: {2}) |-> x]
====
