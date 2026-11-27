---- MODULE missing_module_first ----
\* A module used that is missing is an error before one of meaning.
EXTENDS NoSuchModule
P == [{1} - {2}]
====
