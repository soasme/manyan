---- MODULE postcondition_option_missing ----
\* -postCondition naming no operator of its module: TLC's exception.
\* options: -postCondition Naturals!Done
VARIABLE x
Init == x = 0
Next == x' = x
====
INIT Init
NEXT Next
