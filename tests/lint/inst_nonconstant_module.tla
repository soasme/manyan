---- MODULE inst_nonconstant_module ----
\* A module asserting something above constant level is not constant:
\* as SANY, its constants are substituted by constants only.
VARIABLE x
I == INSTANCE NonConst WITH c <- x
====
