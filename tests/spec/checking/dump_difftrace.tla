---- MODULE dump_difftrace ----
\* -dump dot with -difftrace labels a successor with what changed, and
\* gives it the whole state as its tooltip.
\* options: -difftrace -dump dot states
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x < 2 /\ x' = x + 1 /\ UNCHANGED y
====
INIT Init
NEXT Next
CHECK_DEADLOCK FALSE
