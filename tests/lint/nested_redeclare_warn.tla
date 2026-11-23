---- MODULE nested_redeclare_warn ----
CONSTANT C
VARIABLE x
---- MODULE Sub ----
CONSTANT C
VARIABLE x
A == x = C
====
====
