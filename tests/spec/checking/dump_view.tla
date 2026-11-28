---- MODULE dump_view ----
\* -dump dot with -view labels each state with its view, as its tooltip;
\* with -difftrace a successor's label is the state. -dump writes the view.
\* options: -deadlock -view -difftrace -dump dot states
EXTENDS Naturals
VARIABLES x, steps
Init == x = 0 /\ steps = 0
Next == x' = (x + 1) % 3 /\ steps' = steps + 1
V == x
====
INIT Init
NEXT Next
VIEW V
