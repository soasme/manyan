---- MODULE stack_cfg_set ----
\* Regression for #19: nested sets in .cfg must respect -stack.
\* options: -stack 20
CONSTANT C
VARIABLE x
Init == x = C
Next == x' = x
====
CONSTANT C = {{{{{{{{{{{{{{{{{{{{{{{{{1}}}}}}}}}}}}}}}}}}}}}}}}}
INIT Init
NEXT Next
