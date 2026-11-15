---- MODULE memo_effects ----
\* A constant operator whose body loops is computed once for each
\* argument: TLC computes it at each call, the same unless it prints or
\* reads the run. An argument that prints is evaluated where the body
\* needs it, and one that would fail, unused, does not.
EXTENDS Integers, TLC
VARIABLE x
Divides(p, q) == \E d \in 1..q : q = p * d
Loud(n) == PrintT(<<"loud", n>>) /\ \E d \in 1..n : d = n
Quiet(n, m) == \E d \in 1..n : d = n
First(n, m) == PrintT(<<"first", n>>) /\ \E d \in 1..m : d = m
Below(n) == {d \in 1..n : d < TLCGet("level")}
Init == x = 1
Next == x < 3 /\ x' = x + 1
Inv == /\ Divides(2, 4) /\ Divides(2, 4)
       /\ Loud(2) /\ Loud(2)
       /\ Quiet(1, 1 \div 0) /\ Quiet(1, 1 \div 0)
       /\ First(1, IF PrintT("arg") THEN 2 ELSE 3)
       /\ PrintT(<<"below", x, Below(3)>>)
====
INIT Init
NEXT Next
INVARIANT Inv
