---- MODULE io_utils_empty ----
\* Regression for #20: IOExec(<<>>) must raise Index 0 out of bounds, not crash child.
EXTENDS IOUtils
VARIABLE x
Init == x = IOExec(<<>>)
Next == x' = x
====
INIT Init
NEXT Next
