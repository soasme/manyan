---- MODULE invlevel ----
\* -invlevel N: the invariant that TLCGet("level") < N, so the first
\* behavior of N states is the counterexample.
\* options: -invlevel 3
VARIABLE x
Init == x = "a"
Next == x' = IF x = "a" THEN "b" ELSE "c"
====
INIT Init
NEXT Next
