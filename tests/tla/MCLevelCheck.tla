--------------------------- MODULE MCLevelCheck --------------------------------
(* Exhaustive check of Manyan's higher-order / INSTANCE level-checking summary
   algorithm across all combinations of contexts, argument shapes, and levels. *)
EXTENDS LevelCheck

AllCtxs     == {"id", "prime", "set", "enabled", "always"}
AllArgKinds == {"c0", "v1", "p2", "t3", "v", "set_v", "en_v", "pr_v"}
AllLevels   == 0..3
================================================================================
CONSTANT Ctxs <- AllCtxs
CONSTANT ArgKinds <- AllArgKinds
CONSTANT Levels <- AllLevels
SPECIFICATION Spec
INVARIANT Sound ExactWeightOne
CHECK_DEADLOCK FALSE
