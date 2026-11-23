---- MODULE inst_bad_subst ----
---- MODULE Inner ----
CONSTANT a
Op == a
====
INSTANCE Inner WITH b <- 1, a <- 2
====
