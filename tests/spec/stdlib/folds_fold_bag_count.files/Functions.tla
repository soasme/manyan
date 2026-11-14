---- MODULE Functions ----
\* CommunityModules' folds of a function, which TLC computes in Java.
FoldFunction(op(_, _), base, fun) == base
FoldFunctionOnSet(op(_, _), base, fun, indices) == base
====
