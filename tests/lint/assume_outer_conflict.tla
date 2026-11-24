---- MODULE assume_outer_conflict ----
\* Regression for #16: named ASSUME shadowed in inner module.
ASSUME A == TRUE
---- MODULE Inner ----
A == 1
====
====
