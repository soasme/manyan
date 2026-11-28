---- MODULE unassigned_postcondition_continue ----
\* With -continue TLC sets up no trace spec: a successor that leaves a
\* variable out stops the simulator, and the configured postcondition
\* fails in Java printing the behavior's null.
\* options: -simulate num=1 -depth 5 -seed 1 -continue
EXTENDS TLC, TLCExt
VARIABLES x, y
Init == x = 1 /\ y = 1
Next == x' = 2
Post == PrintT(CounterExample)
====
INIT Init
NEXT Next
POSTCONDITION Post
