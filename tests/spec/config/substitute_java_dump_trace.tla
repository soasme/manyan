---- MODULE substitute_java_dump_trace ----
\* -dumpTrace's modules load Integers, so with -continue too TLC takes
\* Naturals' operators from its class.
\* options: -continue -dumpTrace json trace.json
EXTENDS Naturals
CONSTANT C
VARIABLE x
Foo == 1 + "a"
Init == x = C
Next == x' = x
====
CONSTANT C <- Foo
INIT Init
NEXT Next
