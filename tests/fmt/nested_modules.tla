---- MODULE nested_modules ----
EXTENDS Naturals
CONSTANT N

\* First nested module
---- MODULE InnerA ----
EXTENDS Sequences
A(x) == <<x>>
----
B == A(1)
====

\* Second nested module
---- MODULE InnerB ----
C == N + 1
====

IA == INSTANCE InnerA
IB == INSTANCE InnerB
Main == IA!B = <<1>> /\ IB!C = N + 1
====
