---------------------------------- MODULE Fmt ----------------------------------
(* Core invariants of Manyan's canonical TLA+ formatter (manyan.c, needs_parens,
   fmt_expr, fmt_comments_before and fmt_trailing).

   1. Expression parenthesization: given ASTs built from TLA+'s operator classes
      -- prefix (~ [4,4], -. [12,12]), infix left-assoc (+ [10,10], /\ [3,3]),
      infix non-assoc (= [5,5], => [1,1]), postfix (' [15,15]), and open-ended
      (IF) -- Format emits tokens using manyan.c's exact needs_parens rules.
      A recursive-descent parser enforcing TLA+'s precedence intervals and
      open-ended right-operand grammar must parse Format(ast) back to the exact
      same AST (RoundTrip), and formatting that AST again must emit the exact
      same tokens (Idempotent).

   2. Comment-stream preservation: given a sequence of non-overlapping AST
      spans and any sorted stream of comments before, between, trailing, or
      after spans, the formatter's monotonic cursor (fmt_comments_before +
      fmt_trailing + final flush) must emit every comment exactly once in its
      original order (CommentsPreserved). *)
EXTENDS Naturals, Sequences

CONSTANTS Exprs,      \* finite set of ASTs to test
          CommentCases \* finite set of [spans, comments] test cases

VARIABLE c   \* [expr, ccase]
vars == <<c>>

-------------------------------------------------------------------------------
(* Operator table matching op_table in manyan.c. *)
PREFIX  == "prefix"
INFIX   == "infix"
POSTFIX == "postfix"

OpInfo(op) ==
    CASE op = "~"       -> [name |-> "~",       fix |-> PREFIX,  lo |-> 4,  hi |-> 4,  left |-> FALSE]
      [] op = "ENABLED" -> [name |-> "ENABLED", fix |-> PREFIX,  lo |-> 4,  hi |-> 15, left |-> FALSE]
      [] op = "[]"      -> [name |-> "[]",      fix |-> PREFIX,  lo |-> 4,  hi |-> 15, left |-> FALSE]
      [] op = "-."      -> [name |-> "-.",      fix |-> PREFIX,  lo |-> 12, hi |-> 12, left |-> FALSE]
      [] op = "+"       -> [name |-> "+",       fix |-> INFIX,   lo |-> 10, hi |-> 10, left |-> TRUE]
      [] op = "/\\"     -> [name |-> "/\\",     fix |-> INFIX,   lo |-> 3,  hi |-> 3,  left |-> TRUE]
      [] op = "="       -> [name |-> "=",       fix |-> INFIX,   lo |-> 5,  hi |-> 5,  left |-> FALSE]
      [] op = "=>"      -> [name |-> "=>",      fix |-> INFIX,   lo |-> 1,  hi |-> 1,  left |-> FALSE]
      [] op = "'"       -> [name |-> "'",       fix |-> POSTFIX, lo |-> 15, hi |-> 15, left |-> FALSE]

IsOpenEnded(e) == e.kind = "if"
IsAtomicForPostfix(e) == e.kind = "var"

(* Exact translation of needs_parens in manyan.c (lines 24225-24273). *)
NeedsParens(ch, p, isRight, openOk) ==
    IF IsOpenEnded(ch) THEN
        ~(p.fix = INFIX /\ isRight /\ openOk)
    ELSE IF ch.kind # "op" THEN
        FALSE
    ELSE LET ci == OpInfo(ch.op)
         IN CASE p.fix = POSTFIX -> TRUE
              [] p.fix = PREFIX ->
                   IF ci.fix = INFIX THEN
                       IF p.name = "~" THEN TRUE ELSE ~(ci.lo > p.hi)
                   ELSE IF ci.fix = PREFIX THEN
                       IF p.name = "-." /\ ci.name = "-." THEN TRUE
                       ELSE IF p.name = "ENABLED" THEN ~(ci.lo > p.hi)
                       ELSE IF ci.lo > p.hi THEN FALSE
                       ELSE IF ci.name = p.name /\ p.name \in {"~", "[]"} THEN FALSE
                       ELSE TRUE
                   ELSE FALSE
              [] OTHER ->   \* INFIX parent
                   IF ~isRight THEN
                       IF ci.fix = INFIX THEN
                           IF ci.lo > p.hi THEN FALSE
                           ELSE IF ci.name = p.name /\ p.left THEN FALSE
                           ELSE TRUE
                       ELSE IF ci.fix = PREFIX THEN ~(p.hi < ci.lo)
                       ELSE FALSE
                   ELSE
                       IF ci.fix = INFIX THEN ~(ci.lo > p.hi)
                       ELSE IF ci.fix = PREFIX THEN
                           IF ci.name = "-." /\ p.hi >= 12 THEN TRUE
                           ELSE IF p.left /\ p.hi >= ci.lo THEN TRUE
                           ELSE FALSE
                       ELSE FALSE

RECURSIVE FmtExpr(_, _)
FmtChild(ch, p, isRight, openOk) ==
    LET childOpen == IF isRight THEN openOk ELSE FALSE
        par == NeedsParens(ch, p, isRight, childOpen)
    IN IF par THEN <<"(" >> \o FmtExpr(ch, TRUE) \o <<")">>
       ELSE FmtExpr(ch, childOpen)

FmtExpr(e, openOk) ==
    CASE e.kind = "var" -> <<e.name>>
      [] e.kind = "if"  -> <<"IF">> \o FmtExpr(e.args[1], TRUE) \o <<"THEN">> \o FmtExpr(e.args[2], TRUE)
      [] e.kind = "op"  ->
           LET p == OpInfo(e.op)
           IN CASE p.fix = PREFIX ->
                     <<e.op>> \o FmtChild(e.args[1], p, TRUE, openOk)
                [] p.fix = POSTFIX ->
                     IF IsAtomicForPostfix(e.args[1])
                     THEN FmtExpr(e.args[1], FALSE) \o <<e.op>>
                     ELSE <<"(">> \o FmtExpr(e.args[1], TRUE) \o <<")", e.op>>
                [] OTHER ->
                     FmtChild(e.args[1], p, FALSE, FALSE) \o <<e.op>> \o FmtChild(e.args[2], p, TRUE, openOk)

-------------------------------------------------------------------------------
(* TLA+ precedence parser matching parse_expr in manyan.c.
   Returns [ok, node, pos] where pos is the next unconsumed token index. *)
PrefixOps == {"~", "-.", "ENABLED", "[]"}
InfixOps  == {"+", "/\\", "=", "=>"}

RECURSIVE ParsePrec(_, _, _)
ParseAtom(toks, pos) ==
    IF pos > Len(toks) THEN [ok |-> FALSE, node |-> "err", pos |-> pos]
    ELSE LET t == toks[pos]
         IN CASE t = "(" ->
                   LET r == ParsePrec(toks, pos + 1, 0)
                   IN IF r.ok /\ r.pos <= Len(toks) /\ toks[r.pos] = ")"
                      THEN [ok |-> TRUE, node |-> r.node, pos |-> r.pos + 1]
                      ELSE [ok |-> FALSE, node |-> "err", pos |-> r.pos]
              [] t = "IF" ->
                   LET c1 == ParsePrec(toks, pos + 1, 0)
                   IN IF ~c1.ok \/ c1.pos > Len(toks) \/ toks[c1.pos] # "THEN"
                      THEN [ok |-> FALSE, node |-> "err", pos |-> c1.pos]
                      ELSE LET c2 == ParsePrec(toks, c1.pos + 1, 0)
                           IN IF ~c2.ok THEN [ok |-> FALSE, node |-> "err", pos |-> c2.pos]
                              ELSE [ok |-> TRUE,
                                    node |-> [kind |-> "if", args |-> <<c1.node, c2.node>>],
                                    pos |-> c2.pos]
              [] t \in PrefixOps ->
                   LET info == OpInfo(t)
                       \* Reject adjacent -. -. without parens (would lex as --)
                       adjNeg == t = "-." /\ pos + 1 <= Len(toks) /\ toks[pos + 1] = "-."
                       \* Same repeatable prefix (~ ~, [] []) may chain; ENABLED may not
                       sameRep == t \in {"~", "[]"} /\ pos + 1 <= Len(toks) /\ toks[pos + 1] = t
                       sub == IF sameRep THEN ParsePrec(toks, pos + 1, info.lo)
                              ELSE ParsePrec(toks, pos + 1, info.hi + 1)
                   IN IF adjNeg THEN [ok |-> FALSE, node |-> "err", pos |-> pos]
                      ELSE IF ~sub.ok THEN sub
                      ELSE [ok |-> TRUE, node |-> [kind |-> "op", op |-> t, args |-> <<sub.node>>], pos |-> sub.pos]
              [] t \in {"x", "y"} ->
                   [ok |-> TRUE, node |-> [kind |-> "var", name |-> t], pos |-> pos + 1]
              [] OTHER ->
                   [ok |-> FALSE, node |-> "err", pos |-> pos]

RECURSIVE ParsePostfix(_, _, _)
ParsePostfix(toks, node, pos) ==
    IF pos <= Len(toks) /\ toks[pos] = "'"
    THEN ParsePostfix(toks, [kind |-> "op", op |-> "'", args |-> <<node>>], pos + 1)
    ELSE [ok |-> TRUE, node |-> node, pos |-> pos]

RECURSIVE ParseLoop(_, _, _, _)
ParseLoop(toks, lhs, pos, minPrec) ==
    IF pos > Len(toks) \/ toks[pos] \notin InfixOps
    THEN [ok |-> TRUE, node |-> lhs, pos |-> pos]
    ELSE LET info == OpInfo(toks[pos])
         IN IF info.lo < minPrec
            THEN [ok |-> TRUE, node |-> lhs, pos |-> pos]
            ELSE LET rhs == ParsePrec(toks, pos + 1, info.hi + 1)
                 IN IF ~rhs.ok THEN rhs
                    ELSE LET combined == [kind |-> "op", op |-> info.name, args |-> <<lhs, rhs.node>>]
                             \* Non-associative overlapping-precedence chain is a parse error in SANY
                             badChain == ~info.left /\ rhs.pos <= Len(toks) /\ toks[rhs.pos] \in InfixOps
                                         /\ OpInfo(toks[rhs.pos]).hi >= info.lo
                                         /\ OpInfo(toks[rhs.pos]).lo <= info.hi
                         IN IF badChain THEN [ok |-> FALSE, node |-> "err", pos |-> rhs.pos]
                            ELSE ParseLoop(toks, combined, rhs.pos, minPrec)

ParsePrec(toks, pos, minPrec) ==
    LET a == ParseAtom(toks, pos)
    IN IF ~a.ok THEN a
       ELSE LET pf == IF a.node.kind = "var" \/ (pos <= Len(toks) /\ toks[pos] = "(")
                      THEN ParsePostfix(toks, a.node, a.pos)
                      ELSE a
            IN ParseLoop(toks, pf.node, pf.pos, minPrec)

Parse(toks) ==
    LET r == ParsePrec(toks, 1, 0)
    IN IF r.ok /\ r.pos = Len(toks) + 1 THEN [ok |-> TRUE, node |-> r.node]
       ELSE [ok |-> FALSE, node |-> "err"]

-------------------------------------------------------------------------------
(* Comment-stream preservation model (fmt_comments_before + fmt_trailing).
   A comment is [pos, line, inline]; a span is [pos, eline]. *)
RECURSIVE TakeBefore(_, _, _)
TakeBefore(cs, ci, limit) ==
    IF ci <= Len(cs) /\ cs[ci].pos < limit
    THEN LET r == TakeBefore(cs, ci + 1, limit)
         IN [ci |-> r.ci, out |-> <<cs[ci]>> \o r.out]
    ELSE [ci |-> ci, out |-> <<>>]

RECURSIVE TakeTrailing(_, _, _)
TakeTrailing(cs, ci, line) ==
    IF ci <= Len(cs) /\ cs[ci].line = line /\ cs[ci].inline
    THEN LET r == TakeTrailing(cs, ci + 1, line)
         IN [ci |-> r.ci, out |-> <<cs[ci]>> \o r.out]
    ELSE [ci |-> ci, out |-> <<>>]

RECURSIVE WalkSpans(_, _, _, _)
WalkSpans(spans, cs, i, ci) ==
    IF i > Len(spans) THEN TakeBefore(cs, ci, 9999).out
    ELSE LET b == TakeBefore(cs, ci, spans[i].pos)
             t == TakeTrailing(cs, b.ci, spans[i].eline)
         IN b.out \o t.out \o WalkSpans(spans, cs, i + 1, t.ci)

-------------------------------------------------------------------------------
Init == c \in [expr : Exprs, ccase : CommentCases]
Next == UNCHANGED vars
Spec == Init /\ [][Next]_vars

Formatted == FmtExpr(c.expr, TRUE)
Parsed    == Parse(Formatted)

RoundTrip         == Parsed.ok /\ Parsed.node = c.expr
Idempotent        == Parsed.ok /\ FmtExpr(Parsed.node, TRUE) = Formatted
CommentsPreserved == WalkSpans(c.ccase.spans, c.ccase.comments, 1, 1) = c.ccase.comments
================================================================================
