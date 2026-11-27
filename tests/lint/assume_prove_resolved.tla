---- MODULE assume_prove_resolved ----
\* A theorem's ASSUME ... PROVE is resolved, its NEW names in scope after
\* them: as SANY, c is unknown past a nested ASSUME ... PROVE.
THEOREM ASSUME ASSUME NEW c PROVE c, TRUE PROVE c
====
