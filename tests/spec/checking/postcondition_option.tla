---- MODULE postcondition_option ----
\* -postCondition M!Op extends the root with M and checks Op once the search
\* is done, after the configuration's postconditions; M's constants are
\* evaluated as the root's are.
\* options: -postCondition Post!Done
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 4
Holds == TLCGet("distinct") > 0
====
INIT Init
NEXT Next
POSTCONDITION Holds
