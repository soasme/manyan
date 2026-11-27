---- MODULE recursive_undefined_last ----
\* A RECURSIVE symbol never defined is SANY's error once the module is
\* resolved: the variable declared in its section comes first.
RECURSIVE F(_)
VARIABLE x
====
