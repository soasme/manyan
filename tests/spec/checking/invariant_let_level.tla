---- MODULE invariant_let_level ----
\* SANY gives LET its body's level, but TLC bounds it by its definitions'
\* too: an invariant LET ... IN FALSE over a variable is checked on the
\* states, not computed once as the configuration is read.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Inv == LET y == x + 1 IN FALSE
====
INIT Init
NEXT Next
INVARIANT Inv
