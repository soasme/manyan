---- MODULE dump_trace_invariant_error ----
\* So does an error evaluating an invariant, the behavior to the state.
\* options: -simulate num=2 -depth 5 -seed 7 -dumpTrace tla trace.tla
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == CHOOSE b \in BOOLEAN : b /\ x < 2
====
INIT Init
NEXT Next
INVARIANT Inv
