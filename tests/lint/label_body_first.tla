---- MODULE label_body_first ----
\* A label's expression is resolved before its parameters, as SANY.
F(a) == lab(b) :: a = b
====
