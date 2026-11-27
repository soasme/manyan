---- MODULE defined_twice ----
\* An operator defined again: SANY warns that it duplicates the first,
\* then rejects it.
VARIABLE x
Init == x = 0
Init == x = 1
Next == x' = x
====
INIT Init
NEXT Next
