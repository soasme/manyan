---- MODULE dump_trace_json_initial ----
\* An initial state violating an invariant: a trace of one state and no
\* action.
\* options: -dumpTrace json trace.json
VARIABLE x
Init == x = <<1, "a">>
Next == UNCHANGED x
Inv == x[1] = 2
====
INIT Init
NEXT Next
INVARIANT Inv
