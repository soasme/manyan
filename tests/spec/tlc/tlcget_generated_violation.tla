---- MODULE tlcget_generated_violation ----
\* After an invariant fails, a postcondition reads the states generated
\* as TLC counts them.
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 1}
Next == \/ x' = (x + 1) % 7
        \/ x' = (x + 2) % 7
        \/ x' = (x + 3) % 7
Small == x < 5
Post == PrintT(<<"generated", TLCGet("generated"), TLCGet("distinct")>>)
====
INIT Init
NEXT Next
INVARIANT Small
POSTCONDITION Post
