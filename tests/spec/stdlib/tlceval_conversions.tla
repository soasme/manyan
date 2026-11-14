---- MODULE tlceval_conversions ----
\* TLCEval converts its value as TLC does: an interval enumerated, a tuple, record or function a function of its pairs.
EXTENDS Naturals, Sequences, TLC
ASSUME PrintT(<<TLCEval(1..3), TLCEval(<<1, 2>>), TLCEval(<<>>), TLCEval([a |-> 1]), TLCEval([x \in {1, 2} |-> x]), TLCEval(<<1, 2>>) = <<1, 2>>, Append(TLCEval(<<1>>), 2), DOMAIN TLCEval(<<1, 2>>)>>)
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
INIT Init
NEXT Next
