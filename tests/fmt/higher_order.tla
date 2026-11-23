---- MODULE higher_order ----
EXTENDS Naturals, Sequences

Apply1(F(_), x) == F(x)
Apply2(F(_, _), x, y) == F(x, y)
ApplyOps(_ ++ _, -. _, _ ^+, x, y) == (x ++ y) + (-. x) + (y^+)

Plus == Apply2( + , 1, 2)
Times == Apply2( * , 2, 3)
Minus == Apply2( - , 5, 2)
And == Apply2(/\, TRUE, FALSE)
Not == Apply1(~, FALSE)
Lam == Apply2(LAMBDA a, b : a + b, 3, 4)
====
