---- MODULE dump_trace_json_none ----
\* With no error, -dumpTrace json writes nothing.
\* options: -dumpTrace json trace.json
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1 - x
====
INIT Init
NEXT Next
