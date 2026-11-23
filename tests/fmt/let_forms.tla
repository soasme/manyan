---- MODULE let_forms ----
EXTENDS Naturals
VARIABLE x

SingleFlat == LET a == 1 IN a + 1

MultiDef ==
    LET a == 1
        b == a + 2
        c(k) == k * b
    IN  c(x)

WithRecursive ==
    LET RECURSIVE Sum(_)
        Sum(n) == IF n = 0 THEN 0 ELSE n + Sum(n - 1)
    IN  Sum(x)

WithLocalAndOps ==
    LET LOCAL helper == 2
        a ++ b == a + b + helper
        Rec[n \in 0..3] == IF n = 0 THEN 0 ELSE n + Rec[n - 1]
    IN  Rec[3] ++ x

WithInstance ==
    LET I == INSTANCE Inner
    IN  I!Op + x
====
