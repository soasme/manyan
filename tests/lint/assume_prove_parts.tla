---- MODULE assume_prove_parts ----
\* Parts of an ASSUME ... PROVE, by number or label, as SANY selects them:
\* in the scope of its NEW names, or before them; SUFFICES e has e alone.
THEOREM T == ASSUME TRUE, NEW c \in lab :: {}, ASSUME FALSE PROVE TRUE PROVE c = c
<1>1. SUFFICES ASSUME NEW d PROVE d = d
  BY T!1, T!lab, T!3!2, T!4
<1>2. ASSUME NEW e PROVE e = e
  BY <1>2!2, T!2
<1> QED BY <1>1!1!2, T!3
P == T!1 /\ T!lab = {}
====
