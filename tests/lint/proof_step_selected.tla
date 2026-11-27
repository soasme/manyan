---- MODULE proof_step_selected ----
\* A CASE step named alone is a fact, but no expression: SANY's error.
THEOREM TRUE
<1>1. CASE TRUE
<1>2. <1>1 => TRUE
  BY <1>1
<1> QED
====
