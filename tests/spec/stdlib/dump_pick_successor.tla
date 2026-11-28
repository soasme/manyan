---- MODULE dump_pick_successor ----
\* A step to a state PickSuccessor marked explored is to a state seen:
\* -dump dot writes the step, but not the state.
\* options: -dump dot states
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
A == x' = x + 1
B == x' = x + 2
Next == A \/ B
Pick == PickSuccessor(x' < 2)
====
INIT Init
NEXT Next
ACTION_CONSTRAINT Pick
