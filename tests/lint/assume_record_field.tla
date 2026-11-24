---- MODULE assume_record_field ----
\* Regression for #16: named ASSUME with same identifier as record field.
ASSUME A == TRUE
R == [A |-> 1]
====
