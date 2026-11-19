---- MODULE tlcget_named_undefined ----
\* A named register nothing was kept in.
EXTENDS TLC
ASSUME TLCSet("s:a", 1)
ASSUME TLCGet("s:b") = 1
====
