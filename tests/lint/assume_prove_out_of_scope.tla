---- MODULE assume_prove_out_of_scope ----
\* A part of an ASSUME ... PROVE in the scope of a NEW, from outside it:
\* SANY's error.
THEOREM T == ASSUME NEW c PROVE c = 2
P == T!2
====
