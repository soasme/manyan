---- MODULE tlceval_record_field ----
\* TLCEval of a record is a function, its missing field as one.
EXTENDS Naturals, Sequences, TLC
ASSUME PrintT(TLCEval([a |-> 1]).b)
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
INIT Init
NEXT Next
