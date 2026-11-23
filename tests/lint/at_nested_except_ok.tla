---- MODULE at_nested_except_ok ----
CONSTANT f
A == [f EXCEPT ![1] = [@ EXCEPT ![2] = @]]
====
