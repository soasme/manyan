---- MODULE proof_def_entry ----
\* A DEF clause names an operator, not a constant: SANY's error.
CONSTANT c
THEOREM TRUE
BY DEF c
====
