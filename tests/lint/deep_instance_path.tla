---- MODULE deep_instance_path ----
\* Regression for #13: >32 nested INSTANCE chain in resolve_path.
---- MODULE M0 ----
A == 1
====
---- MODULE M1 ----
I == INSTANCE M0
====
---- MODULE M2 ----
INSTANCE M1
====
---- MODULE M3 ----
INSTANCE M2
====
---- MODULE M4 ----
INSTANCE M3
====
---- MODULE M5 ----
INSTANCE M4
====
---- MODULE M6 ----
INSTANCE M5
====
---- MODULE M7 ----
INSTANCE M6
====
---- MODULE M8 ----
INSTANCE M7
====
---- MODULE M9 ----
INSTANCE M8
====
---- MODULE M10 ----
INSTANCE M9
====
---- MODULE M11 ----
INSTANCE M10
====
---- MODULE M12 ----
INSTANCE M11
====
---- MODULE M13 ----
INSTANCE M12
====
---- MODULE M14 ----
INSTANCE M13
====
---- MODULE M15 ----
INSTANCE M14
====
---- MODULE M16 ----
INSTANCE M15
====
---- MODULE M17 ----
INSTANCE M16
====
---- MODULE M18 ----
INSTANCE M17
====
---- MODULE M19 ----
INSTANCE M18
====
---- MODULE M20 ----
INSTANCE M19
====
---- MODULE M21 ----
INSTANCE M20
====
---- MODULE M22 ----
INSTANCE M21
====
---- MODULE M23 ----
INSTANCE M22
====
---- MODULE M24 ----
INSTANCE M23
====
---- MODULE M25 ----
INSTANCE M24
====
---- MODULE M26 ----
INSTANCE M25
====
---- MODULE M27 ----
INSTANCE M26
====
---- MODULE M28 ----
INSTANCE M27
====
---- MODULE M29 ----
INSTANCE M28
====
---- MODULE M30 ----
INSTANCE M29
====
---- MODULE M31 ----
INSTANCE M30
====
---- MODULE M32 ----
INSTANCE M31
====
---- MODULE M33 ----
INSTANCE M32
====
---- MODULE M34 ----
INSTANCE M33
====
---- MODULE M35 ----
INSTANCE M34
====
---- MODULE M36 ----
INSTANCE M35
====
---- MODULE M37 ----
INSTANCE M36
====
---- MODULE M38 ----
INSTANCE M37
====
---- MODULE M39 ----
INSTANCE M38
====
---- MODULE M40 ----
INSTANCE M39
X == I!A
====
====
