---- MODULE DieHard ----
\* Measure 4 gallons with a 3-gallon jug and a 5-gallon jug.
\* NotSolved is violated: the trace is a solution.
EXTENDS Naturals
VARIABLES small, big
Min(m, n) == IF m < n THEN m ELSE n
Init == small = 0 /\ big = 0
Next == \/ small' = 3 /\ big' = big
        \/ big' = 5 /\ small' = small
        \/ small' = 0 /\ big' = big
        \/ big' = 0 /\ small' = small
        \/ LET p == Min(small, 5 - big) IN small' = small - p /\ big' = big + p
        \/ LET p == Min(big, 3 - small) IN big' = big - p /\ small' = small + p
NotSolved == big # 4
====
