---- MODULE Inner ----
EXTENDS Naturals
VARIABLE z
IInit == z = 0
INext == z < 1 /\ z' = z + 1
ISpec == IInit /\ [][INext]_z
====
