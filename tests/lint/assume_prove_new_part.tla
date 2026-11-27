---- MODULE assume_prove_new_part ----
\* A NEW of an ASSUME ... PROVE is no expression, nor are its parts.
THEOREM T == ASSUME NEW c \in {} PROVE TRUE
THEOREM TRUE BY T!1
P == T!1!1
====
