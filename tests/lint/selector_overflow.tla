---- MODULE selector_overflow ----
\* Regression for #37: selector > INT32_MAX must not truncate to SEL_LL (!<<).
EXTENDS Naturals
A == 1 + 2
B == A!4294967295
====
