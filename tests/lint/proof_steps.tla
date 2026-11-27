---- MODULE proof_steps ----
\* A proof's steps parse as SANY's: levels, <+> and <*>, step names as
\* facts with or without a period, every kind of step.
THEOREM TRUE
<1>1 TRUE
  <+> QED
<1> DEFINE F == 1
<1> G(a) == a
<1> TAKE a, b \in {}
<1> PICK c \in {} : TRUE
<1> HAVE TRUE
<1> WITNESS 1, 2
<1> CASE TRUE
<1>2. SUFFICES ASSUME NEW d PROVE TRUE
  OBVIOUS
<1> USE <1>1 DEF F
<*> QED BY <1>1, <1>2 DEF F, G
====
