---- MODULE Post ----
EXTENDS Naturals, TLC
Started == PrintT("started")
Done == TLCGet("distinct") < 3
====
