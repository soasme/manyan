---- MODULE assume_prove_expression ----
\* The name of an ASSUME ... PROVE is a fact, not an expression.
THEOREM T == ASSUME NEW c PROVE c
THEOREM TRUE
BY T
P == T
====
