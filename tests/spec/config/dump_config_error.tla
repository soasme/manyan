---- MODULE dump_config_error ----
\* TLC makes the -dump dot file as it starts: a run that fails before its
\* states leaves the graph's head, unclosed.
\* options: -dump dot states
VARIABLE x
Init == x = 0
Next == x' = x
====
INIT Init
NEXT Next
INVARIANT Missing
