---- MODULE Log ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
A == PrintT("logA")
Entries == <<>>
Init == x = Len(Entries) + Len(Entries)
Next == UNCHANGED x
====
