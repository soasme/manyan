---- MODULE inst_dup_subst ----
---- MODULE Inner ----
CONSTANT a
Op == a
====
INSTANCE Inner WITH a <- 1, a <- 2
====
