---- MODULE folds_fold_bag_count ----
\* An error in one of CommunityModules' folds or searches, as TLC's Java
\* reports it.
EXTENDS Naturals, Sequences, SequencesExt, Functions, BagsExt, TLC
ASSUME PrintT(FoldBag(LAMBDA x, y: x, 0, [a |-> 0]))
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
INIT Init
NEXT Next
