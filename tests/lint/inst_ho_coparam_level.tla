---- MODULE inst_ho_coparam_level ----
VARIABLE x
Bar(a) == {a}
I == INSTANCE Sub WITH Op <- Bar, v <- [](x = 1)
====
