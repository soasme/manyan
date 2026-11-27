---- MODULE instance_operator_arg ----
\* I!F of an instance with parameters, where an operator is: as TLC, an
\* operator of I's parameters and then F's; and a LET's instance with
\* parameters, applied, sees them and the LET's scope.
EXTENDS TLC, Naturals
I(a) == INSTANCE Pair WITH y <- a
G(Op(_, _)) == Op(1, 2)
K == INSTANCE Applies WITH Op <- I!Leib
F(n) == LET Z(b) == INSTANCE Pair WITH y <- b + n IN Z(1)!Leib(2)
ASSUME PrintT(<<G(I!Leib), K!Val, F(10), LET Z(b) == INSTANCE Pair WITH y <- b IN G(Z!Leib)>>)
====
