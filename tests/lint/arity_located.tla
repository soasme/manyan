---- MODULE arity_located ----
\* Too many arguments: SANY's error is at the parentheses around them,
\* and names the operator as written.
EXTENDS Naturals
I(k) == INSTANCE Inner WITH K <- k
x == I(1)!G(1, (2))
====
