---- MODULE reprint_counterexample_simulate ----
\* A simulation prints the behavior it kept: Init and Next do not print
\* again, as they do where TLC rebuilds a model-checking counterexample.
\* options: -simulate num=1 -depth 14 -seed 74
EXTENDS Naturals, TLC
VARIABLE l
Init == l = 1 /\ PrintT(<<"init">>)
Next == l < 4 /\ l' = l + 1 /\ PrintT(<<"step", l>>)
Spec == Init /\ [][Next]_l
P == <>(l = 5)
====
SPECIFICATION Spec
PROPERTY P
CHECK_DEADLOCK FALSE
