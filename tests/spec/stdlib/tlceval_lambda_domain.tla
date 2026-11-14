---- MODULE tlceval_lambda_domain ----
\* TLCEval of [x \in S |-> e] is a function of its pairs, applied outside its domain as one.
EXTENDS Naturals, Sequences, TLC
ASSUME PrintT(TLCEval([x \in {1, 2} |-> x])[3])
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
INIT Init
NEXT Next
