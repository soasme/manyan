---- MODULE dump_alias_error ----
\* An ALIAS failing as TLC writes an initial state's dot label: an error of
\* the state it was adding, the label cut where it failed.
\* options: -dump dot states
VARIABLE x
Init == x \in {0, 1}
Next == x' = x
Alias == [_format |-> IF x = 0 THEN "%s=%s;" ELSE "%s %s %s", x |-> x]
====
INIT Init
NEXT Next
ALIAS Alias
