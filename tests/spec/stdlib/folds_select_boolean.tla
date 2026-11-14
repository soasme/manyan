---- MODULE folds_select_boolean ----
\* An error in one of CommunityModules' folds or searches, as TLC's Java
\* reports it.
EXTENDS Naturals, Sequences, SequencesExt, Functions, BagsExt, TLC
ASSUME PrintT(SelectLastInSeq(<<1, 2>>, LAMBDA x: x))
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
INIT Init
NEXT Next
