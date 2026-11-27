---- MODULE record_keyword_field ----
\* As SANY and TLC, the first field of a record constructor may be a keyword.
EXTENDS TLC
ASSUME PrintT(<<[OTHER |-> 1], [IF |-> 2].IF, [TRUE |-> 3, b |-> 4], DOMAIN [LET |-> 5]>>)
====
