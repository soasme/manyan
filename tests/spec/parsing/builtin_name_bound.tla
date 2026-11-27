---- MODULE builtin_name_bound ----
\* SANY reads TRUE, FALSE, BOOLEAN and STRING as names where it expects
\* one, and rejects a name bound so as it resolves it: a semantic error.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = CHOOSE BOOLEAN \in {1} : TRUE
====
INIT Init
NEXT Next
