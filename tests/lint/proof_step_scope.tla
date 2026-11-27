---- MODULE proof_step_scope ----
\* A step's name is in the steps after it, not past its proof.
THEOREM TRUE
<1>1. TRUE
  <2>1. TRUE
  <2>2. QED BY <2>1
<1>2. QED BY <1>1, <2>1
====
