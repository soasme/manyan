---- MODULE builtin_name_defined ----
\* A definition of TRUE: SANY's semantic error, over the whole definition.
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == LET TRUE == 1 IN x' = x
====
INIT Init
NEXT Next
