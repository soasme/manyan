# A reference semantics of TLA⁺

TLC is the de facto interpreter of TLA⁺, and Manyan prints what TLC
prints. But TLC can be wrong. This is a definition of what constant
expressions mean that does not depend on TLC, in Lean 4, for any tool
to be tested against. It follows *Specifying Systems* (chapter 16) and
the definitions of the standard modules.

```sh
lake build                       # .lake/build/bin/ref
echo '{x \in 1..5 : x % 2 = 1}' | .lake/build/bin/ref
{1, 3, 5}
printf '<<>>[1]\n' | .lake/build/bin/ref
undefined: a function applied outside its domain
```

A line `EXPR<TAB>VALUE` asks whether `EXPR` equals `VALUE`: `same`, or
`differs: ` and its value. `make fuzz-ref` sends it random expressions
with the values Manyan prints for them.

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

Both are the same `sem`, so the two cannot drift apart. What is not
proved yet is that `Oracle.exec` refines `Oracle.classical χ` for every
`χ`, and so that every value `ref` prints is TLA⁺'s.

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
