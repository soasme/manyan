---- MODULE proof_suffices_scope ----
\* SUFFICES ASSUME's NEW names are in the steps after it, not in its proof.
THEOREM TRUE
<1>1. SUFFICES ASSUME NEW a PROVE a
  BY a
<1>2. QED BY a
====
