---- MODULE proof_star_step ----
\* A theorem's steps may be <0>; <*>a names step a of the level it is
\* among; a step named <*>a or <+>a is SANY's error.
THEOREM TRUE
<0>a. TRUE
<0> QED BY <*>a
THEOREM TRUE
<1>a. TRUE
<1>b. TRUE
  <2>a. TRUE
  <2> QED BY <*>a, <1>a
<1> QED BY <*>b
THEOREM TRUE
<+>b. TRUE
<*> QED
====
