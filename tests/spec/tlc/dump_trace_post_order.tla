---- MODULE dump_trace_post_order ----
\* TLC checks the command line's postconditions, -dumpTrace's, before the
\* configuration's.
\* options: -dumpTrace json trace.json
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Small == x < 2
Post == PrintT(<<"post", TLCGet("distinct")>>)
====
INIT Init
NEXT Next
INVARIANT Small
POSTCONDITION Post
