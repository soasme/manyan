---- MODULE replaced_again ----
\* Computed first by its own name, a definition is computed again for the
\* name it replaces, at startup and at each use.
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Read == IF PrintT("read") THEN <<1, 2>> ELSE <<>>
Entries == <<>>
Init == x = Len(Entries) + Len(Entries) + Len(Read)
Next == UNCHANGED x
Spec == Init /\ [][Next]_x
====
SPECIFICATION Spec
CONSTANT Entries <- Read
