# A reference semantics of TLA⁺

TLC is the de facto interpreter of TLA⁺, and Manyan prints what TLC
prints. But TLC can be wrong. This is a definition of what expressions,
actions and temporal formulas mean that does not depend on TLC, in Lean 4, for any tool
to be tested against. It follows *Specifying Systems* (chapter 16) and
the definitions of the standard modules.

```sh
lake build                       # .lake/build/bin/ref
lake build Ref.Sound             # checks the proof below
echo '{x \in 1..5 : x % 2 = 1}' | .lake/build/bin/ref
{1, 3, 5}
printf '<<>>[1]\n' | .lake/build/bin/ref
undefined: a function applied outside its domain
```

A line `EXPR<TAB>VALUE` asks whether `EXPR` equals `VALUE`: `same`, or
`differs: ` and its value. `make fuzz-ref` sends it random expressions
with the values Manyan prints for them.

## Models

```sh
.lake/build/bin/ref model M.tla M.cfg U [TRACE]
```

checks the model `M.tla` with `M.cfg` as TLA⁺ means it, `U` a
definition of `M` naming the universe, a set of records of the variables
that every behavior stays in (`Ref/Check.lean`). Its initial states are
those of `U` that the initial predicate holds of. A step is a pair of
them that the specification's `[][N]_v` allows, so `ENABLED`, `x' \in S`
and a subscript that leaves a variable out mean what they mean in TLA⁺.
It prints the distinct reachable states, the depth, the least depth of
each violated invariant and of a deadlock, and whether each temporal
property holds. A property is decided as a formula of linear-time
temporal logic over the state graph: its negation's tableau and the
graph have a product with a fair cycle, or not. With `TRACE`, a
behavior Manyan prints, it also says whether that is a behavior of the
specification that shows the error. Modules beside `M.tla` that it
extends or instantiates are read too: `I!D` is `D` with the
substitutions of `I == INSTANCE N WITH v <- e`. `CONSTRAINT` is TLC's, not TLA⁺'s:
a state outside it is checked against the invariants, and not
explored.

## One definition, two oracles

`sem O n ρ e` (`Ref/Sem.lean`) is the value of `e`. Some questions
have answers no program computes, like whether `\A x \in Nat : P` holds,
or which value `CHOOSE` picks. The oracle `O` answers them:

- `Oracle.classical χ` answers each one as TLA⁺ does, with `χ` the
  choice function. `sem (Oracle.classical χ)` is the definition, and it
  is not computable.
- `Oracle.exec` answers what it can compute and says `unknown` to the
  rest. `sem Oracle.exec` is the reference that runs, specialized to
  finite values the way TLC is.

Both are the same `sem`, so the two cannot drift apart, and
`Ref/Sound.lean` proves that they agree: where `sem Oracle.exec` has a
value, `sem (Oracle.classical χ)` has no other, for every `χ`
(`sem_agree`). The proof follows the evaluator one level at a time, as
`exec` answers only where every choice function answers alike: `CHOOSE`
among the elements of an enumerated set when exactly one satisfies it.

`CHOOSE` in an enumerated set is χ's choice among the elements that
satisfy it, as the enumeration has them, each value once. That this is
TLA⁺'s choice rests on the evaluator respecting `=` (a value equal to
another evaluates as it does), which is not proved.

## What it decides

- `undefined`: TLA⁺ does not say what the value is, so any value is
  right. This covers `<<>>[1]`, `Tail(<<>>)`, `CHOOSE x \in {} : TRUE`,
  `0 ^ 0`, `1 \div 0`, a set or function TLA⁺ leaves unspecified, and
  `1 = "a"`. TLA⁺ does not say that values of different kinds differ:
  a string might be a set. Applying a non-Boolean with logic is undefined
  too, as in `FALSE /\ <<>>[1]`, even though TLC answers `FALSE`.
- `unknown`: TLA⁺ says what the value is, but the reference cannot
  compute it. That covers a quantifier over `Nat`, or `CHOOSE` among
  several values, whose value only the choice function knows.
- Where the semantics is exact and TLC is stricter, the reference gives
  the semantics. `[f EXCEPT ![k] = e]` with `k` outside the domain is
  `f`, as `[x \in DOMAIN f |-> IF x = k ...]` is. `LET y == <<>>[1] IN 3`
  is 3, and `[{} -> Int]` is `{<<>>}`.

A value Manyan prints that the reference says `differs` is a bug in
Manyan, even where TLC prints the same thing. On a verdict, the
semantics wins. Presentation, meaning how a value or error is printed,
stays TLC's.
