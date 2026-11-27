---- MODULE instance_twice ----
\* An instance defined again as it was: SANY warns of each definition it
\* brings, in its context's order, then of the instance, and keeps the first.
I == INSTANCE Inner WITH C <- 1
I == INSTANCE Inner WITH C <- 2
====
