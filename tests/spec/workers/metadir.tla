---- MODULE metadir ----
\* options: -workers 4 -metadir meta
\* Workers sharing the files of meta: the whole state graph.
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == \/ x' = (x + 1) % 30 /\ UNCHANGED y
        \/ y' = (y + 1) % 30 /\ UNCHANGED x
====
INIT Init
NEXT Next
