---- MODULE proof_module_name ----
\* MODULE M in a proof: one loaded, or nested before; SANY's error else.
EXTENDS TLC
THEOREM TRUE
BY MODULE Naturals, MODULE proof_module_name
THEOREM TRUE
BY MODULE Inner
---- MODULE Inner ----
====
====
