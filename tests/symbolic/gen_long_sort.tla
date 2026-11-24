---- MODULE gen_long_sort ----
\* Regression for #21: Gen() with >53-char uninterpreted type sort name must not NULL-deref.
EXTENDS Apalache
VARIABLE
  \* @type: Set(AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA);
  s
Init == s = Gen(1)
Next == s' = s
Inv == s = {}
====
INIT Init
NEXT Next
INVARIANT Inv
