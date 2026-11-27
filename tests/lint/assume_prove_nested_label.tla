---- MODULE assume_prove_nested_label ----
\* No label after the NEW of a nested ASSUME ... PROVE, as SANY.
THEOREM T == ASSUME NEW c, ASSUME NEW d PROVE lab :: d = c PROVE TRUE
====
