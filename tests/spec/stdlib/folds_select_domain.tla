---- MODULE folds_select_domain ----
\* An error in one of CommunityModules' folds or searches, as TLC's Java
\* reports it.
EXTENDS Naturals, Sequences, SequencesExt, Functions, BagsExt, TLC
ASSUME PrintT(SelectInSubSeq(<<1, 2>>, 1, 3, LAMBDA x: TRUE))
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
INIT Init
NEXT Next
