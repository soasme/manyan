---- MODULE let_instance_nested ----
\* A nested module instantiated in a LET: as SANY, defined twice.
---- MODULE Inner ----
A == TRUE
====
P == LET M == INSTANCE Inner IN M!A
====
