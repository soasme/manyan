---- MODULE proof_instance_step ----
\* An INSTANCE step brings the module's definitions into the steps after:
\* as SANY, one of a name again of its arity a warning, else an error.
Z == 2
THEOREM TRUE
<1> INSTANCE Pair WITH y <- 1
<1> INSTANCE Pair WITH y <- 2
<1>1. Leib(1) = {1}
<1> QED BY <1>1 DEF Leib
THEOREM ASSUME NEW Leib PROVE TRUE
<1> INSTANCE Pair WITH y <- 1
<1> QED
====
