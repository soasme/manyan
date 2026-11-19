---- MODULE tlcset_upstream ----
\* TLC's test-model/TLCSet.tla with TLCSetPost.cfg, as of 1.8.0 (bc1b506):
\* its counters, named registers and TLCGet("spec"), less what Manyan
\* leaves out by decision: TLCGet("config").fingerprint, and its worker,
\* which is the number of workers given; and TLC's coverage, which its
\* test enables. Its harness runs TLC with -deadlock.
\* options: -deadlock
EXTENDS Integers, TLC

ASSUME TLCGet("config").mode = "bfs"

ASSUME TLCGet("spec").inits = {[name |-> "Init", location |-> [beginLine |-> 21, beginColumn |-> 9, endLine |-> 32, endColumn |-> 40, module |-> "tlcset_upstream"]]}

ASSUME TLCGet("spec").actions = {[name |-> "Next", location |-> [beginLine |-> 34, beginColumn |-> 9, endLine |-> 51, endColumn |-> 41, module |-> "tlcset_upstream"]]}

ASSUME TLCSet("s:counter", 0)
ASSUME TLCSet("s:label", "hello")

VARIABLES x

Init == /\ x = 0
        \* Old world
        /\ TLCGet("duration") >= 0 \* Init might take more than a seconds since startup.
        /\ TLCGet("diameter") = 1
        /\ TLCGet("queue") = 0 \* queue is always empty because spec is a single behavior.
        /\ TLCGet("distinct") = 0
        \* New world
        /\ TLCGet("stats").duration >= 0
        /\ TLCGet("stats").queue = 0
        /\ TLCGet("stats").distinct = 0
        /\ TLCGet("stats").diameter = 1
        /\ TLCGet("stats").generated = 0

Next == /\ x' = x + 1
        /\ TLCSet("exit", x = 4223)
        \* Old world
        /\ TLCGet("duration") >= 0 \* Next might evaluate within the first second of model checking.
        /\ TLCGet("queue") = 0 \* queue is always empty because spec is a single behavior.
        /\ TLCGet("distinct") = x'
        /\ TLCGet("generated") = x'
        /\ TLCGet("diameter") = x' \* As byproduct check that trace is strictly monotonically increasing.
        \* Named registers
        /\ TLCGet("s:counter") = x
        /\ TLCGet("s:label") = "hello"
        /\ TLCSet("s:counter", x')
        \* New world
        /\ TLCGet("stats").duration >= 0
        /\ TLCGet("stats").queue = 0
        /\ TLCGet("stats").distinct = x' 
        /\ TLCGet("stats").diameter = x'
        /\ TLCGet("stats").generated = x'

Spec == Init /\ [][Next]_x

PostCondition ==
    /\ TLCGet("s:label") = "hello"
    /\ TLCGet("s:counter") \in Nat

ASSUME TLCGet("config").deadlock = FALSE
ASSUME TLCGet("config").seed \in STRING

ASSUME TLCGet("spec").temporals = {}
ASSUME TLCGet("spec").invariants = {}
ASSUME TLCGet("spec").impliedinits = {}
ASSUME TLCGet("spec").impliedtemporals = {}

ASSUME TLCGet("revision").tag \in STRING
ASSUME TLCGet("revision").count \in Nat
ASSUME TLCGet("revision").timestamp \in Nat
ASSUME TLCGet("revision").date \in STRING
ASSUME TLCGet("revision").calver \in STRING
ASSUME TLCGet("revision").calver # ""
ASSUME TLCGet("revision").tag = "development" => TLCGet("revision").count = 0 
ASSUME TLCGet("revision").tag # "development" => TLCGet("revision").count > 7854
ASSUME TLCGet("revision").tag # "development" => TLCGet("revision").timestamp > 1626748578
====
SPECIFICATION
Spec
POSTCONDITION PostCondition
