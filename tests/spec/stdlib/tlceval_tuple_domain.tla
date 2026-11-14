---- MODULE tlceval_tuple_domain ----
\* TLCEval of a tuple is a function, applied outside its domain as one: etcd's trace validation.
EXTENDS Naturals, Sequences, TLC
ASSUME PrintT(TLCEval(<<1, 2>>)[3])
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
INIT Init
NEXT Next
