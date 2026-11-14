---- MODULE folds_fold_function_value ----
\* An error in one of CommunityModules' folds or searches, as TLC's Java
\* reports it.
EXTENDS Naturals, Sequences, SequencesExt, Functions, BagsExt, TLC
ASSUME PrintT(FoldFunction(LAMBDA x, y: x, 0, {1}))
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
INIT Init
NEXT Next
