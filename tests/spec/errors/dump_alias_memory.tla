---- MODULE dump_alias_memory ----
\* An ALIAS too wide for TLC's memory as it writes an initial state's dot
\* label: TLC exits, the file as it began.
\* options: -dump dot states
VARIABLE x
Init == x = 0
Next == x' = 1
Alias == [x |-> x, _format |-> "%2147483647s"]
====
INIT Init
NEXT Next
ALIAS Alias
