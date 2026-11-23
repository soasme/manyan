---- MODULE inst_ho_level_not_met ----
VARIABLE x
Bar(a) == {a}
I == INSTANCE Sub WITH Op <- Bar, v <- x
====
