---- MODULE instance_unnamed_redefined ----
\* A definition of a symbol an unnamed INSTANCE brought: as SANY, a
\* warning located at the INSTANCE, then an error.
VARIABLE x
INSTANCE UnnamedMid WITH y <- x
Init == x = 2
====
