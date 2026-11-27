---- MODULE inst_var_action ----
\* A variable instantiated by an action, though nothing primes it there.
VARIABLE x
K == INSTANCE PathC WITH u <- x'
====
