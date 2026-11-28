---- MODULE alias_not_record_difftrace ----
\* An alias that is not a record leaves the state as it is: with -difftrace
\* a state but the last shows what changed, and so does a dot label.
\* options: -difftrace -dump dot states
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y
Inv == x < 3
Alias == x
====
INIT Init
NEXT Next
INVARIANT Inv
ALIAS Alias
