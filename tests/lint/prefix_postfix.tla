---- MODULE prefix_postfix ----
\* A postfix operator on the operand of a prefix one that binds as
\* tightly: as SANY, a precedence conflict.
VARIABLE x
P == ENABLED x'
====
