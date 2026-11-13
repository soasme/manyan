---- MODULE view_fairness ----
\* Under a VIEW a fairness condition's action is evaluated on the step to
\* the successor itself, not to the state kept with its view: CA goes to
\* pc = "a" with one step more, never to the kept one with 0, yet it is taken.
EXTENDS Naturals
VARIABLES pc, steps
vars == <<pc, steps>>
Init == pc = "a" /\ steps = 0
AB == pc = "a" /\ pc' = "b" /\ steps' = steps + 1
BC == pc = "b" /\ pc' = "c" /\ steps' = steps + 1
CA == pc = "c" /\ pc' = "a" /\ steps' = steps + 1
Next == AB \/ BC \/ CA
Spec == Init /\ [][Next]_vars /\ WF_vars(AB) /\ WF_vars(BC) /\ SF_vars(CA)
Exits == <>(pc = "d")
PcOnly == pc
====
SPECIFICATION Spec
PROPERTY Exits
VIEW PcOnly
