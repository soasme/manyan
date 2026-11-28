---- MODULE dump_error_again ----
\* TLC expands a state that failed again to report where: -dump dot writes
\* its steps, to states seen now, once more.
\* options: -dump dot states
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == \/ x' = x
        \/ x' = 1
        \/ x = 0 /\ x' = 1 \div 0
====
INIT Init
NEXT Next
