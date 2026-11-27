---- MODULE set_tuple_in ----
\* { <<a, e>> \in S } with no colon: SANY's error at the tuple.
CONSTANTS a, e, S
P == {<<a, e>> \in S}
====
