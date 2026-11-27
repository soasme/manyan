---- MODULE inst_path_level ----
\* I(a)!J(b)!D is one operator: an instance's parameter is bounded only
\* where D uses it, its arguments counted along the path.
VARIABLE x
I(z) == INSTANCE PathA WITH y <- z
Ok == I(x')!J(1)!No
P == I(1)!J(x')!Baz
====
