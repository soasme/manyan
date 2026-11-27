---- MODULE label_illegal_param ----
\* A label's parameter that names nothing: SANY's error at it.
P == \A a \in {1}, b \in (l(a) :: {2}) : a = b
====
