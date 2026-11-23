---- MODULE inst_non_leibniz ----
---- MODULE Inner ----
CONSTANT F(_)
Op == F(1)
====
INSTANCE Inner WITH F <- ENABLED
====
