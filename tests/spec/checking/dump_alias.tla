---- MODULE dump_alias ----
\* -dump dot labels each state through the ALIAS, its tooltip the state.
\* options: -dump dot states
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Alias == [_format |-> "%s is %s;", x |-> x, double |-> 2 * x]
====
INIT Init
NEXT Next
ALIAS Alias
CHECK_DEADLOCK FALSE
