---- MODULE inst_level_exceed ----
---- MODULE Inner ----
VARIABLE v
Op == v' = v
====
VARIABLE x
INSTANCE Inner WITH v <- x'
====
