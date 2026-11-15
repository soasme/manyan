---- MODULE random_fingerprint ----
\* Model checking draws for each state from -seed and the state's
\* fingerprint under the -fp polynomial, as TLC.
\* options: -seed 3 -fp 4
EXTENDS Naturals, TLC
VARIABLE x, y
Init == x = 0 /\ y = RandomElement(1..1000)
Next == x < 4 /\ x' = x + 1 /\ y' = RandomElement(1..1000)
Inv == PrintT(<<x, y>>)
====
INIT Init
NEXT Next
INVARIANT Inv
