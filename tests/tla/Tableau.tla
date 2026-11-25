------------------------------ MODULE Tableau ---------------------------------
(* How Manyan simplifies and expands a temporal formula into a tableau
   (manyan.c, tf_simplify, expand, and tnode_expand) and accepts a behavior
   with it (accept_component's eventualities). A formula is in negation normal
   form over literals (a predicate, its negation, or true/false). Simplify
   folds temporal and boolean constants and idempotent connectives. A tableau
   node holds the literals that hold now and the formulas that must hold from
   the next state on. Expanding runs alpha rules (literals, /\, []) before
   beta rules (\/, <>), prunes contradictions early, and skips beta formulas
   already satisfied in lits or next (Manna & Pnueli §5.5). The initial nodes
   expand Simplify(c.f), a node's successors its next formulas.

   On a lasso, a behavior that loops back from its last state, a position
   and a node whose literals hold there make a node of the product, its
   successors the next position with each successor node. The tableau
   accepts the lasso when a strongly connected component of the product,
   reachable from an initial node at the first position, has an edge
   inside and, for each eventuality <>A, a node that does not defer it.
   It must accept exactly the lassos the unsimplified formula holds on. *)
EXTENDS Integers, Sequences

CONSTANTS Formulas,   \* [op, args]: op "p", "~p", "q", "~q", "true", "false", or "and", "or", "always", "eventually"
          Lassos      \* [w, loop]: w a sequence of the sets of predicates true in each state

VARIABLE c   \* [f, l], the formula and lasso checked
vars == <<c>>

Lit(op) == [op |-> op, args |-> <<>>]
IsLit(f) == f.args = <<>>
Neg(op) == CASE op = "p" -> "~p" [] op = "~p" -> "p" [] op = "q" -> "~q" [] op = "~q" -> "q"

Node(lits, next) == [lits |-> lits, next |-> next]

RECURSIVE Simplify(_)
Simplify(f) ==
    CASE IsLit(f) -> f
      [] f.op \in {"always", "eventually"} ->
            LET a == Simplify(f.args[1])
            IN IF a.op \in {"true", "false"} THEN a ELSE [op |-> f.op, args |-> <<a>>]
      [] f.op = "and" ->
            LET a == Simplify(f.args[1])
                b == Simplify(f.args[2])
            IN CASE a.op = "false" \/ b.op = "false" -> Lit("false")
                 [] a.op = "true" -> b
                 [] b.op = "true" \/ a = b -> a
                 [] OTHER -> [op |-> "and", args |-> <<a, b>>]
      [] f.op = "or" ->
            LET a == Simplify(f.args[1])
                b == Simplify(f.args[2])
            IN CASE a.op = "true" \/ b.op = "true" -> Lit("true")
                 [] a.op = "false" -> b
                 [] b.op = "false" \/ a = b -> a
                 [] OTHER -> [op |-> "or", args |-> <<a, b>>]

RECURSIVE Expand(_, _, _)
Expand(todo, lits, next) ==
    IF todo = {} THEN {Node(lits, next)}
    ELSE LET alphas == {f \in todo : f.op \notin {"or", "eventually"}}
             f == CHOOSE f \in (IF alphas # {} THEN alphas ELSE todo) : TRUE
             rest == todo \ {f}
         IN CASE f.op = "true" -> Expand(rest, lits, next)
              [] f.op = "false" -> {}
              [] IsLit(f) ->
                    IF Lit(Neg(f.op)) \in lits THEN {} ELSE Expand(rest, lits \cup {f}, next)
              [] f.op = "and" -> Expand(rest \cup {f.args[1], f.args[2]}, lits, next)
              [] f.op = "always" -> Expand(rest \cup {f.args[1]}, lits, next \cup {f})
              [] f.op = "or" ->
                    IF f.args[1] \in lits \/ f.args[2] \in lits \/ f.args[1] \in next \/ f.args[2] \in next
                    THEN Expand(rest, lits, next)
                    ELSE Expand(rest \cup {f.args[1]}, lits, next) \cup Expand(rest \cup {f.args[2]}, lits, next)
              [] f.op = "eventually" ->
                    IF f.args[1] \in lits \/ f \in next
                    THEN Expand(rest, lits, next)
                    ELSE Expand(rest \cup {f.args[1]}, lits, next) \cup Expand(rest, lits, next \cup {f})

Succs(n) == Expand(n.next, {}, {})

w == c.l.w
L == Len(w)
After(i) == IF i < L THEN i + 1 ELSE c.l.loop

Holds(lit, i) == IF lit.op \in {"p", "q"} THEN lit.op \in w[i] ELSE Neg(lit.op) \notin w[i]
Admits(n, i) == \A lit \in n.lits : Holds(lit, i)

Step(x) == {<<After(x[1]), m>> : m \in {m \in Succs(x[2]) : Admits(m, After(x[1]))}}

(* The product nodes reachable from X, X included. *)
RECURSIVE Closure(_)
Closure(X) == LET Y == X \cup UNION {Step(x) : x \in X}
              IN IF Y = X THEN X ELSE Closure(Y)
Reach(x) == Closure(Step(x))   \* by one edge or more

Product == Closure({<<1, n>> : n \in {n \in Expand({Simplify(c.f)}, {}, {}) : Admits(n, 1)}})

Defers(x, e) == e \in x[2].next
Eventualities(C) == {e \in UNION {x[2].next : x \in C} : e.op = "eventually"}

(* A component with an edge inside, each of its eventualities met. *)
Accepting(x) == LET C == {y \in Product : y = x \/ (y \in Reach(x) /\ x \in Reach(y))}
                IN /\ x \in Reach(x)
                   /\ \A e \in Eventualities(C) : \E y \in C : ~Defers(y, e)
Accepts == \E x \in Product : Accepting(x)

(* The formula on the lasso from position i. *)
Future(i) == (i..L) \cup (c.l.loop..L)
RECURSIVE Sat(_, _)
Sat(f, i) == CASE f.op = "true" -> TRUE
               [] f.op = "false" -> FALSE
               [] IsLit(f) -> Holds(f, i)
               [] f.op = "and" -> Sat(f.args[1], i) /\ Sat(f.args[2], i)
               [] f.op = "or" -> Sat(f.args[1], i) \/ Sat(f.args[2], i)
               [] f.op = "always" -> \A j \in Future(i) : Sat(f.args[1], j)
               [] f.op = "eventually" -> \E j \in Future(i) : Sat(f.args[1], j)

Init == c \in [f : Formulas, l : Lassos]
Next == UNCHANGED vars
Spec == Init /\ [][Next]_vars

Same == Accepts = Sat(c.f, 1)
================================================================================
