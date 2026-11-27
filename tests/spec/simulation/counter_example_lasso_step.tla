---- MODULE counter_example_lasso_step ----
\* options: -simulate num=1 -depth 23 -seed 874
\* semantics: TLC's lasso goes back from s = 3 to s = 2, a step Next does not allow
\* The cycle of a simulation's counterexample is a cycle of its behavior.
VARIABLE s
Succ == <<{2, 3}, {1, 3}, {1}>>
Init == s = 2
Next == s' \in Succ[s]
Spec == Init /\ [][Next]_s
P == <>[][s' \in {1, 2}]_s
====
SPECIFICATION Spec
PROPERTY P
