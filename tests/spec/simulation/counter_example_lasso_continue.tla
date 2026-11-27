---- MODULE counter_example_lasso_continue ----
\* With -continue, a simulation's lasso is kept for a postcondition:
\* only a safety violation's behavior is not.
\* options: -simulate num=3 -depth 6 -seed 3 -continue
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Live == <>(x = 7)
Post == PrintT(CounterExample)
====
SPECIFICATION Spec
PROPERTY Live
POSTCONDITION Post
