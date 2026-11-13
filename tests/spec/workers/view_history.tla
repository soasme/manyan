---- MODULE view_history ----
\* Under a VIEW, the state kept for a view is the first one found with it,
\* as one process finds it: workers must not keep another. hist, which the
\* VIEW leaves out, shows which one was kept.
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Procs, K
VARIABLES pc, flag, cnt, mode, hist
Init == /\ pc = [p \in Procs |-> "idle"]
        /\ flag = [p \in Procs |-> FALSE]
        /\ cnt = [p \in Procs |-> 0]
        /\ mode = [p \in Procs |-> "a"]
        /\ hist = <<>>
Tick(p) == /\ pc[p] = "idle" /\ cnt[p] < K
           /\ cnt' = [cnt EXCEPT ![p] = @ + 1]
           /\ UNCHANGED <<pc, flag, mode>>
Switch(p) == /\ pc[p] = "idle"
             /\ mode' = [mode EXCEPT ![p] = IF @ = "a" THEN "b" ELSE IF @ = "b" THEN "c" ELSE "a"]
             /\ UNCHANGED <<pc, flag, cnt>>
Check(p) == /\ pc[p] = "idle" /\ cnt[p] = K /\ mode[p] = "c"
            /\ \A q \in Procs \ {p} : ~flag[q]
            /\ pc' = [pc EXCEPT ![p] = "set"]
            /\ UNCHANGED <<flag, cnt, mode>>
Set(p) == /\ pc[p] = "set"
          /\ flag' = [flag EXCEPT ![p] = TRUE]
          /\ pc' = [pc EXCEPT ![p] = "crit"]
          /\ UNCHANGED <<cnt, mode>>
Exit(p) == /\ pc[p] = "crit"
           /\ flag' = [flag EXCEPT ![p] = FALSE]
           /\ pc' = [pc EXCEPT ![p] = "idle"]
           /\ cnt' = [cnt EXCEPT ![p] = 0]
           /\ UNCHANGED mode
Next == \E p \in Procs : /\ Tick(p) \/ Switch(p) \/ Check(p) \/ Set(p) \/ Exit(p)
                         /\ hist' = Append(hist, p)
View == <<pc, flag, cnt, mode>>
Mutex == Cardinality({p \in Procs : pc[p] = "crit"}) <= 1
====
CONSTANTS
  Procs = {1, 2, 3, 4}
  K = 4
INIT Init
NEXT Next
VIEW View
INVARIANT Mutex
