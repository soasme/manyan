---- MODULE instance_arg_arity ----
\* I!F of an instance with parameters, where an operator is: of arity
\* I's and F's together.
I(a) == INSTANCE Pair WITH y <- a
G(Op(_)) == Op(1)
P == G(I!Leib)
====
