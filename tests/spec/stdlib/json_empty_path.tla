---- MODULE json_empty_path ----
\* Regression for #20: JsonSerialize("", ...) must not read past strdup("").
EXTENDS Json
VARIABLE x
Init == x = JsonSerialize("", <<1>>)
Next == x' = x
====
INIT Init
NEXT Next
