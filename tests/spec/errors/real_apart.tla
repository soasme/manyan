---- MODULE real_apart ----
\* A decimal written apart, 2. 3: as SANY reads it, a real, which TLC
\* cannot handle.
EXTENDS TLC
ASSUME PrintT(2. 3)
====
