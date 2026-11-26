# The Manyan TLA⁺ Standard

Version 0.1. The language Manyan accepts and the results it must produce.

## Contents

- [1 Scope](#1-scope)
- [2 Conformance](#2-conformance)
- [3 Lexical structure](#3-lexical-structure)
- [4 Modules](#4-modules)
- [5 Declarations and definitions](#5-declarations-and-definitions)
- [6 Expressions](#6-expressions)
- [7 Values](#7-values)
- [8 Standard modules](#8-standard-modules)
- [9 Model configuration](#9-model-configuration)
- [10 Model checking](#10-model-checking)
- [11 Output](#11-output)
- [12 Exclusions](#12-exclusions)

## 1 Scope

This Standard defines TLA⁺ Version 2 as a model checker must evaluate it:
the syntax of modules, the meaning of the expressions TLC can evaluate,
the model configuration language, the model-checking procedure, and the
observable results. It follows *Specifying Systems* (Lamport, 2002) and the
TLA⁺ Version 2 language changes. Where those leave a choice open (the order
in which values print, which errors are reported, how many states are
counted), TLC 1.8.0 (tla2tools v1.8.0, built from commit bc1b506) decides.

The proof language (§12) is parsed only as far as needed to skip it.

## 2 Conformance

### 2.1 Oracle

TLC 1.8.0 is the oracle. A test of this Standard is a module, a model
configuration, and the output TLC produces for them. An implementation
conforms when, for every test, it produces the same normalized output (§11.1)
and the same exit status (§11.3).

### 2.2 Requirements

An implementation shall

1. accept every module and configuration this Standard defines;
2. produce, for a correct model, the result TLC produces: the same verdict,
   the same counts of states, and the same error traces;
3. report an error where TLC reports one, with the same first line of the
   message for the errors listed in §11.3, and the same exit status;
4. check models with one worker deterministically: the same inputs give the
   same output.

### 2.3 Normative language

*Shall* states a requirement. *Unspecified* means TLC's choice is not part of
this Standard and tests must not depend on it.

## 3 Lexical structure

### 3.1 Characters

A module is ASCII text. Lines end with LF or CR LF. A tab moves to the
column after the next multiple of 8, as SANY counts it. Columns and lines
are numbered from 1.

### 3.2 Module boundaries

Text before the first line that holds `----` (four or more dashes) followed
by `MODULE` is ignored. A module begins `---- MODULE Name ----` (any run of
four or more dashes on each side) and ends with a line of four or more `=`
characters. Text after the end of the outermost module is ignored. A module
may contain nested modules with the same delimiters.

### 3.3 Comments and white space

`\*` starts a comment running to the end of the line. `(*` starts a
comment that ends at the matching `*)`; such comments nest. A line of four
or more `-` inside a module is a separator and is ignored.

### 3.4 Identifiers and keywords

An identifier is a sequence of letters, digits, and `_` that contains at
least one letter and is not all digits followed by a letter-free tail; for
example `x`, `x1`, `_x`, `1a` are identifiers and `12` is a number. The
following are reserved and are not identifiers:

```
ASSUME ASSUMPTION AXIOM BOOLEAN CASE CHOOSE CONSTANT CONSTANTS ELSE
ENABLED EXCEPT EXTENDS FALSE IF IN INSTANCE LET LOCAL MODULE OTHER
STRING SUBSET THEN THEOREM TRUE UNCHANGED UNION VARIABLE VARIABLES
WITH WF_ SF_ LAMBDA RECURSIVE LEMMA PROPOSITION COROLLARY
```

`WF_` and `SF_` are prefixes: `WF_vars` is `WF_` followed by the
subscript `vars`.

### 3.5 Numbers

A numeral is a sequence of decimal digits. `\b`, `\o`, and `\h` (or `\B`,
`\O`, `\H`) introduce binary, octal, and hexadecimal numerals. A decimal
`d.d` is accepted by the grammar. As TLC cannot compute with either, a
spec with a decimal, or with a numeral above 2^31 - 1, anywhere in a
definition, assumption or theorem is an error before checking (§11.3),
whether it is used or not. The first is reported: the modules in the
order they are finished (dependencies first), and in each its
definitions, its inner modules, its assumptions, then its theorems.

### 3.6 Strings

A string is enclosed in `"`. The escapes are `\"`, `\\`, `\n`, `\t`, `\r`,
and `\f`. A string does not span lines.

### 3.7 Operator symbols

The lexer takes the longest symbol that is a token. The symbols are the
punctuation `( ) [ ] { } << >> , : :: . .. ... ! @ ' == |-> -> <- _`
together with the operators of §6.1. Backslash words (`\in`, `\cup`, ...)
are single tokens; an unknown backslash word is an error.

## 4 Modules

### 4.1 Units

A module is a header, an optional `EXTENDS M1, ..., Mn`, and a sequence of
units: declarations (§5.1), definitions (§5.2), `INSTANCE`s (§4.3),
`ASSUME`s (§4.5), theorems (§12), nested modules, and separators.

### 4.2 EXTENDS

`EXTENDS M` makes every non-`LOCAL` symbol of `M`, and of the modules `M`
extends, a symbol of the extending module. A name defined twice with
different definitions is an error; the same definition reached twice is
one symbol.

### 4.3 INSTANCE

`INSTANCE M WITH p1 <- e1, ..., pn <- en` imports the definitions of `M`
with each constant and variable `pi` of `M` replaced by `ei`. A parameter
not listed is replaced by the symbol of the same name in the instantiating
module, which must exist. `N(x) == INSTANCE M WITH ...` defines a module
instance: `N(a)!Op(b)` is `Op` of the instance with `x` bound to `a`. A
`LOCAL` instance or definition is not exported.

### 4.4 Module resolution

A module named in `EXTENDS` or `INSTANCE` is, in order: a nested module in
scope, a file `Name.tla` in the directory of the root module, a
standard module (§8), or, as SANY reads a monolithic spec, the text of the
root module's file from a line `---- MODULE Name ----` to the next line
that starts with `====`, its lines numbered from that `MODULE` line.

### 4.5 ASSUME

`ASSUME e` (or `ASSUMPTION`, `AXIOM`, optionally named `ASSUME N == e`)
states that the constant expression `e` is `TRUE`. Each assumption is
evaluated after the constants are bound (§10.1); a false one is an error
(§11.3).

## 5 Declarations and definitions

### 5.1 Declarations

`CONSTANT c1, ..., cn` declares constant parameters, each a name or an
operator shape such as `F(_, _)` or `_ ** _`. `VARIABLE v1, ..., vn`
declares the state variables. The plural spellings are synonyms.

### 5.2 Operator definitions

`Op == e`, `Op(p1, ..., pn) == e`, and the infix, prefix, and postfix forms
`a ++ b == e`, `-. a == e`, `a ^+ == e` define operators. A parameter may
itself be an operator, written `F(_)` or `_ + _`, and an argument for it is
an operator name (a constant operator's, or an instance's `I!Op`), an
operator parameter, or a `LAMBDA x, y : e`. Arguments are passed by name: the
argument expression is evaluated, in the context of the call, where the
parameter is used, also when the operator called is a parameter; a
built-in operator takes its arguments' values.

### 5.3 Function definitions

`f[x \in S] == e` defines `f` as `CHOOSE f : f = [x \in S |-> e]`: `f` may
appear in `e`, so the function is recursive. Several bound variables
`f[x \in S, y \in T]` define a function on `S \X T`.

### 5.4 Recursive operators

`RECURSIVE Op(_, _)` declares an operator that a later definition in the
same unit list defines; the definition may then refer to itself. Evaluation
that does not terminate is an error (§11.3).

### 5.5 LET

`LET d1 ... dn IN e` makes the definitions `di` (operator, function, or
`RECURSIVE` declarations) visible in later `di` and in `e`.

### 5.6 Scoping

A name is visible only after its declaration or definition; a definition
sees itself only when it defines a function or was declared `RECURSIVE`. So
`LET e == CHOOSE e \in S : TRUE IN e` is legal. A bound name may not reuse a
name already visible in its scope, except that names introduced by different
definitions do not conflict. A name refers to the innermost binding.

A nested module sees the names its enclosing modules declare or define
before it, and may not define them again. It may declare again a constant
or variable they declare, with the same arity; SANY warns of it,
`Multiple declarations or definitions for symbol C.` and where the first
is, each location in the module of its file. After processing each
module of a file, dependencies first, SANY prints every warning so far
under `*** Warnings: N`.

When two extended modules define one name differently, the first
definition is the one used, and SANY warns of the other, `Warning: the
definition of 'R' conflicts with` and where the first is; a definition an
instance brings in gives way too, with `Multiple declarations or
definitions for symbol R.`, located at the definition, or at the statement
of a `LOCAL INSTANCE`. A definition's location runs from its name to the
end of its body; one of a standard module's is where it is in TLC's file.

Once every module is processed, SANY warns, module by module, dependencies
first, of each field of a record or set of records (`[f |-> e]`, `[f : S]`)
named as a definition or declaration its module sees: `The field name "f"
in the record constructor is identical to the existing definition or
declaration`, with where each is. It does not when a record or set of
records of the same fields, in the module or one it extends, has a field
whose expression is built, through the definitions it uses, from a
constant, a variable, a parameter, a bound identifier, `BOOLEAN`, `Nat` or
`Int`.

### 5.7 Labels and subexpressions

`lab :: e` or `lab(x, y) :: e`, at the start of an expression, labels `e`
(which extends as far as possible); `x` and `y` are bound identifiers in
scope. A label changes nothing in the value of `e`.

`Op(a)!s1!s2...` names a subexpression of the definition of `Op` (an
operator, a theorem, or an assumption, possibly reached through instances
`I!Op`). Each selector `si` moves from the current expression to a part:

- a name: after `Op`, after a label, or after a LET definition, a label in
  it (not inside another label or LET definition); otherwise a definition
  of the LET the current expression is, after `:` if it would be a label;
- `:` makes the next name a LET definition;
- `n`, `<<`, `>>`: operand `n` of an operator application, the first, or
  the second of two; a LET expression has its body as only operand, a
  label is transparent, `r.f` has operands `r` and `"f"`, a record its
  values, `[f EXCEPT ...]` only `f`, a CASE arm `p -> e` is selected by
  two selectors (`!1!>>` is `e` of the first arm); for a quantifier,
  `CHOOSE`, set constructor or function constructor, operand `n` is the
  set of the `n`-th group of bound identifiers;
- `(e1, ..., en)` or `@`: the body of a quantifier, `CHOOSE`, set or
  function constructor, its bound identifiers (all of them, tuples
  flattened) as parameters.

The result is an operator whose parameters are, in order, those met on the
way: `Op`'s, each label's, each LET definition's, and the bound
identifiers of each `(...)` or `@`. Arguments given to every selector
(`Op(a)!lab(b)!(c)`) apply it; none at all (`Op!lab!@`) make it an
operator argument. The LET definitions around the subexpression are in
scope in it. `COp(1, 2)!(3)!++(4, 5)` is thus `{a, b, q, p, x}` of
`COp(q, p) == CHOOSE x : LET a ++ b == {a, b, q, p, x} IN ...` with
`q, p, x, a, b` = `1, 2, 3, 4, 5`.

A theorem `THEOREM N == e` or assumption `ASSUME N == e` defines `N` as an
operator `N == e` without parameters.

### 5.8 Levels

Each expression has a level: 0 constant, 1 state (it reads variables), 2
action (it primes), 3 temporal. An operand of `'` or `UNCHANGED` must be of
level at most 1, of `ENABLED` and `\cdot` at most 2; in `[A]_v`,
`<<A>>_v`, `WF_v(A)` and `SF_v(A)`, `A` at most 2 and `v` at most 1. The
operands of the other built-in operators are at most actions: of `=`, `#`,
`\in`, the set operators, set and tuple constructors, function
application, `.f`, `EXCEPT` and its keys, `CHOOSE`, `{x \in S : P}` and
`{e : x \in S}`, and the ranges of every bound; the operands of the logical
operators, `IF`, `CASE`, records `[f |-> e]`, and the bodies of `\A`, `\E`
and `[x \in S |-> e]` may be temporal. `/\`, `\/`, `=>` and `<=>` may not
join a temporal formula and an action. A parameter of a definition allows,
for its argument, the least level its uses allow, and a declaration of a
module the same for what an `INSTANCE` substitutes for it; an argument or a
substitute of higher level is an error (§11.3). A call's level is that of
its definition and of the arguments for the parameters it uses outside
`ENABLED`, so `B(Next)` with `B(d) == ENABLED d` is a state predicate.

## 6 Expressions

### 6.1 Precedence

Each operator has a precedence range `[lo, hi]`. In `a op1 b op2 c`, the
expression parses as `(a op1 b) op2 c` when `op1`'s range lies above
`op2`'s, as `a op1 (b op2 c)` when below, and is an error when the ranges
overlap, unless `op1` and `op2` are the same left-associative operator.

| Operators | Range | Assoc. |
|---|---|---|
| `=>` | 1–1 | |
| `~>` `<=>` `\equiv` `-+->` | 2–2 | |
| `/\` `\land` `\/` `\lor` | 3–3 | left |
| `~` `\lnot` `\neg` (prefix) | 4–4 | |
| `[]` `<>` `ENABLED` `UNCHANGED` (prefix) | 4–15 | |
| `=` `#` `/=` `<` `>` `\leq` `<=` `=<` `\geq` `>=` `\in` `\notin` `\subseteq` `\subset` `\supseteq` `\supset` `\prec` `\succ` `\preceq` `\succeq` `\sim` `\simeq` `\ll` `\gg` `\asymp` `\approx` `\cong` `\sqsubset` `\sqsubseteq` `\sqsupset` `\sqsupseteq` `\doteq` `\propto` `:=` `::=` `|-` `-|` `|=` `=|` | 5–5 | |
| `\cdot` | 5–14 | left |
| `@@` | 6–6 | left |
| `:>` `<:` | 7–7 | |
| `\` | 8–8 | |
| `\cap` `\intersect` `\cup` `\union` | 8–8 | left |
| `SUBSET` `UNION` (prefix) | 8–8 | |
| `..` `...` | 9–9 | |
| `DOMAIN` (prefix) | 9–9 | |
| `!!` | 9–13 | |
| `##` `$` `$$` `??` `\uplus` `\sqcap` `\sqcup` | 9–13 | left |
| `\wr` | 9–14 | |
| `\X` `\times` | 10–13 | n-ary |
| `+` `++` `\oplus` `(+)` | 10–10 | left |
| `%` | 10–11 | |
| `%%` `\|` `\|\|` | 10–11 | left |
| `-` `--` `\ominus` `(-)` | 11–11 | left |
| `-` (prefix) | 12–12 | |
| `*` `**` `&` `&&` `\o` `\circ` `\odot` `(.)` `\otimes` `(\X)` `\star` `\bigcirc` `\bullet` | 13–13 | left |
| `/` `//` `\div` `\oslash` `(/)` | 13–13 | |
| `^` `^^` | 14–14 | |
| `'` `^+` `^*` `^#` (postfix) | 15–15 | |
| `[ ]` (application) | 16–16 | left |
| `.` (record field) | 17–17 | left |

`a \X b \X c` is the ternary product, not `(a \X b) \X c`.

### 6.2 Junction lists

A list of formulas each preceded by `/\` (or each by `\/`), whose bullets are
aligned in one column, is their conjunction (disjunction). An item extends
until the first token that begins at or left of the bullet's column; a token
there that is the same bullet starts the next item, and any other token ends
the list. A parenthesis, bracket, or brace that opened inside an item must
close inside it.

### 6.3 Logic

`TRUE`, `FALSE`, `BOOLEAN` (the set `{FALSE, TRUE}`). `~`, `/\`, `\/`, `=>`,
`<=>` (and `\equiv`) on Booleans. `/\` and `\/` evaluate left to right and
stop at the first operand that decides the result; so do `=>` and junction
lists. An operand that is not a Boolean is an error.

`\A x \in S : p` and `\E x \in S : p` over a finite `S`; several bounds
`\A x, y \in S, z \in T : p`; tuple binders `\E <<x, y>> \in S \X T : p`. The bound sets are computed
first; the bindings follow in the order of §7.4 with the first variable
varying fastest, which decides an action's successors and initial states
in order (§10).
Unbounded `\A x : p` and `\E x : p` are errors to evaluate.
`CHOOSE x \in S : p` is the first element of `S`, in the order of §7.4, that
satisfies `p`; none is an error. `CHOOSE x : p` is evaluable only as
§10.3 permits.

`=` and `#` (`/=`) compare values (§7.3).

### 6.4 Conditionals

`IF c THEN a ELSE b`. `CASE p1 -> e1 [] ... [] pn -> en [] OTHER -> e`
evaluates the guards in order and yields the arm of the first true one;
no true guard and no `OTHER` is an error.

### 6.5 Sets

Enumeration `{a, b}` and `{}`; `\in`, `\notin`; `\cup`, `\cap`, `\`;
`\subseteq`; `SUBSET S` (all subsets); `UNION S` (union of the elements);
`{x \in S : p}` (filter); `{e : x \in S, y \in T}` (image). Membership may
be decided for the infinite sets `Nat`, `Int`, `STRING`, `Seq(S)`,
`SUBSET S`, `[S -> T]`, `[a : S]`, and filters of them; enumerating an
infinite set is an error.

As in TLC, `{x \in S : p}` is computed at once when `S` is reducible: an
interval, or a set of elements that is not one TLC keeps as its
definition. TLC keeps as their definitions `SUBSET S`, `S \X T`,
`[S -> T]`, `[a : S]`, `Seq(S)`, `Nat`, `Int`, `STRING`; `UNION S` unless
`S` and its elements are sets of elements; `S \cup T` unless both are
reducible; `S \cap T` unless one is; `S \ T` unless `S` is; and a filter
of a set that is not reducible. Such a filter is lazy: membership
evaluates `p` for that element only, and `S` may be any value until the
filter is enumerated. A quantifier or `CHOOSE` over a value that is not a
set, or over `Nat`, `Int`, `STRING` or `Seq(S)`, is an error at once; over
another infinite set, the error is that of enumerating it.

`S \subseteq T` tests each element of `S` in `T`, but, as TLC,
`SUBSET A \subseteq SUBSET B` is `A \subseteq B` and an interval is in
an interval when its bounds are. Enumerating `SUBSET S` of an `S` of 31
elements or more fails counting it, as TLC: `Overflow when computing the
number of elements in:` and the set.

A `UNION S` that TLC keeps is taken by quantifiers, set images and
`x \in S` in an action one element of `S` after another, in the standard
order of `S`, with any duplicates; `CHOOSE`, filters and functions take it
sorted. Once it has been counted, fingerprinted, or compared as the left
side of `=` or of the standard order, TLC holds its elements, and
quantifiers take them sorted too.

### 6.6 Functions

`[x \in S |-> e]` and `[x \in S, y \in T |-> e]`; application `f[a]` and
`f[a, b]` (which is `f[<<a, b>>]`); `DOMAIN f`; the function set
`[S -> T]`; `[f EXCEPT ![a] = e, ![b][c] = e2, !.r = e3]`, where `@` in a
replacement is the old value at that path. Applying `f` outside its domain
is an error.

As in TLC, `[x \in S |-> e]` is computed in full where it is evaluated,
except where it stays lazy: in the function position of an application
`f[a]` (directly, or as the value of the operator, LET definition or arm
`f` names), within the body of a lazy function, in a recursive function
definition (§5.3), and over a domain whose sets are not all reducible
(§6.5), such as an infinite one or one that is no set. A function definition that
is not recursive and names no variable is computed in full once, before
checking, if it can be. Applying a lazy function evaluates `e`
at that argument only, so an error elsewhere in its domain is not raised,
and `f[i \in S] == [j \in T |-> ... f[i][k] ...]` may use other values of
`f[i]` within `f[i]`. A lazy function is computed in full when it is
compared, fingerprinted, printed, or taken `DOMAIN` or `EXCEPT` of. One
that cannot be, being over an infinite domain or failing, prints as
`[x \in S |-> <expression LOC>]`: each bound's first name, or `<<a, b>>` for
a tuple pattern, with its domain, then `e` as TLC names an expression:
its location (§11.3), or, for a numeral, the numeral as written. A value
that holds such a function prints on one line. A function of several
bounds is computed with the first bound varying fastest, and an error
message prints it in that order; `Print` and `PrintT` print it sorted.

An EXCEPT path whose key is outside the domain leaves the
value unchanged and prints TLC's warning, `Warning: The EXCEPT was applied
to non-existing fields of the value at` and the location of `f`; the first
warning of a run adds `(Use the -nowarning option to disable this
warning.)`, and a warning already printed is not printed again.
`-nowarning` turns off TLC's warnings: these two, not SANY's.

### 6.7 Records

`[a |-> 1, b |-> 2]` is the function on `{"a", "b"}`; `r.a` is `r["a"]`.
`[a : S, b : T]` is the set of such records.

### 6.8 Tuples

`<<a, b, c>>` is the function on `1..3`. `<<>>` is the empty tuple.
`S \X T` is the set of pairs.

### 6.9 Action operators

In an action, `e'` is `e` evaluated in the next state; `e' = v` and
`e' \in S` assign a variable when `e'`, through definitions without
parameters, `LET`, instances and their substitutions, is `x'` or
`(d)'` with `d` reaching `x` likewise, as TLC's getPrimedVar finds it; `UNCHANGED e` is
`e' = e`; `[A]_e` is `A \/ UNCHANGED e`; `<<A>>_e` is `A /\ ~UNCHANGED e`;
`ENABLED A` is true in a state from which `A` has a successor; `A \cdot B`
is composition, an error unless the Java property
`tlc2.tool.impl.Tool.cdot` is `true`. Then, as TLC: from `s`, the states
`t` that `A` goes to start with `s`'s values of the variables already
assigned and must satisfy the conjuncts after `A \cdot B`, and count as
generated; from each `t`, `B` gives the successors, with those conjuncts
too, each a successor of `s`. As a formula, `A \cdot B` holds of a step
to `u` when `A` goes from `s` to some `t`, starting from no values, from
which the step to `u` satisfies `B`; in `ENABLED`, when `B` is enabled
from some `t`.

Inside `ENABLED`, as in TLC, a primed variable of an instantiated module
written in `A` itself is not replaced by its substitution: `x' = e` gives
the variable named `x` a value, and `x'` reads it back, so with `INSTANCE
M WITH x <- z, y <- z`, `ENABLED (x' = 0 /\ y' = 1)` in `M` is true;
`UNCHANGED x` and the change
`<<A>>_v` requires of `v` compare that variable likewise. An action passed to an
operator argument from outside the instance keeps its substitutions.

### 6.10 Temporal operators

`[]F`, `<>F`, `F ~> G` (`[](F => <>G)`), `WF_e(A)`, `SF_e(A)`, and
`F -+-> G`. Temporal formulas appear only in `SPECIFICATION` and `PROPERTY`
formulas (§10.5), and in definitions they use.

A temporal formula contains no raw action, a semantic error otherwise:
`[]A` and `<>A` of an action `A` must be `[][A]_e` and `<><<A>>_e`; the
operands of `~>` and `-+->` are not actions; and a quantifier over a
temporal formula has no action-level bound.

## 7 Values

### 7.1 Kinds

A value is a Boolean, an integer, a string, a model value (§9.2), a finite
or infinite set, or a function. Tuples, sequences, and records are
functions: `<<1, 2>> = [i \in 1..2 |-> i]` and
`[a |-> 1] = [x \in {"a"} |-> 1]`.

### 7.2 Integers

Integers are the signed 32-bit range of TLC. A result outside it is an
error (§11.3). `\div` and `%` are floor division and its non-negative
remainder; a zero divisor is an error.

### 7.3 Equality

Values of different kinds are unequal only when one is a model value or
when both are sets or both are functions; otherwise comparing them (for
example `1 = "a"`) is an error. Two sets are equal when they have the same
elements; two functions when they have the same domain and values. No
value is an element of an empty interval, such as `1..0`, even one that is
not an integer.

### 7.4 Order

Every set prints and enumerates its elements in the standard order:
Booleans `FALSE` before `TRUE`; integers by value; strings in order of
first appearance (§7.5); model values by declaration order; tuples and
functions by domain size, then element by element; sets by size, then
element by element; `Nat` before `Int`, which equal only themselves.
Elements of different kinds are ordered by kind.

### 7.5 String order

Strings are ordered by when Manyan first meets them, in this order: the
built-in names of the language; the identifiers and numerals of the root
module and then of each module it uses, in the order those modules are
read; the string literals of every module, dependencies first; the
configuration; and finally strings made during checking. Record fields are
strings, so records print their fields in this order too.

### 7.6 Printing

A value prints as an expression that denotes it: `TRUE`, `-3`, `"a\"b"`, a
model value's name, `{1, 2}`, `<<1, 2>>`, `[a |-> 1, b |-> 2]`, and a
function on another domain as `(1 :> "a" @@ 2 :> "b")`. A function whose
domain is `1..n` prints as a tuple and one whose domain is a non-empty set
of strings prints as a record. A printed value longer than the line width
(80) is broken as TLC's pretty printer breaks it: each element of a long
set, tuple, or record on its own line, aligned under the first.

## 8 Standard modules

The standard modules are those of tla2tools, with the operators below
evaluated natively.

- **Naturals**: `Nat`, `+`, `-`, `*`, `^`, `<`, `>`, `\leq`, `\geq`, `%`,
  `\div`, `..`.
- **Integers**: Naturals and `Int`, prefix `-`.
- **Sequences**: `Seq`, `Len`, `\o`, `Append`, `Head`, `Tail`, `SubSeq`,
  `SelectSeq`.
- **FiniteSets**: `IsFiniteSet`, `Cardinality`.
- **Bags**: `IsABag`, `BagToSet`, `SetToBag`, `BagIn`, `EmptyBag`, `(+)`,
  `(-)`, `BagUnion`, `\sqsubseteq`, `BagOfAll`, `BagCardinality`,
  `CopiesIn`, as TLC's Java class: `IsABag` is `FALSE` for any value
  that is no bag, `CopiesIn` yields the count however small,
  `BagUnion({B})` is `B`, and a count is cast to an integer, which fails
  on another value. `SubBag` is its definition.
- **Reals**: TLC's module of placeholders: `Real` is the string
  `"Reals"`, `a / b` is `CHOOSE m \in Real : m * b = a` (an error), and
  `Infinity` an unbounded `CHOOSE`; their definitions are on TLC's lines.
- **TLC**: `Print`, `PrintT`, `Assert`, `JavaTime`, `TLCGet`, `TLCSet`,
  `:>`, `@@`, `Permutations`, `SortSeq`, `RandomElement`, `Any`,
  `ToString`, `TLCEval`.
- **TLCExt**: `AssertError`, `TLCCache`, `TLCModelValue`,
  `TLCGetOrDefault`; `AssertEq`, `TLCNoOp` and `TLCGetAndSet` are their
  definitions. `Trace`, `CounterExample`, `ToTrace`, `TLCFP`,
  `PickSuccessor`, `TLCDefer` and `TLCEvalDefinition` need TLC's own
  traces, fingerprints or successors: Manyan stops, saying it does not
  support the one evaluated.

`RandomElement(S)` and the Randomization operators draw as TLC does, from
`java.util.Random` seeded with `-seed`: the model, the assumptions and
Init in sequence from one generator, as TLC's main thread keeps the one
its first draw made; a state's successors from one seeded with `-seed`
xor the state's fingerprint, which Manyan's fingerprints, not TLC's, make
other draws than TLC's. `RandomSubset(k, S)` takes
k indices from a linear congruential generator, `x' = (a * x + c) % m`
skipping those past |S|: m is the least number from max(|S|, 9) on that is
not divisible by 4 and has a square factor, a is 1 more than the product of
m's prime factors, x starts at a random index and c is a random one of
TLC's 1341 primes (§10.8). An index into a set of functions, records or
tuples is read in the mixed radix of its parts; for one of more than
2^31 - 1 elements the indices are instead `(i * (2^63 - 25) + l) % |S|`,
l the absolute value of a random long. An interval's index i is its lower
bound plus i, and the interval is not made. A negative k is Java's
NegativeArraySizeException, whatever S.

A string is no sequence, but `Len`, `Tail` and `SubSeq` take it as its
characters, and `\o` joins two strings: `Len("ab") = 2`, and `Tail` and
`SubSeq` of a string, and `"ab" \o "c"`, are strings. The other operators
of Sequences fail on a string, as does `\o` of a string and a sequence, and
a string equals no tuple: comparing them is an error (§7.3).

`Print(out, val)` writes `out` and `val` and yields `val`; `PrintT(out)`
writes `out` and yields `TRUE`; `Assert(c, out)` is `TRUE` when `c` is and
otherwise an error (§11.3). Printing a value, and `ToString`, enumerate
the sets in it, so an infinite `S \cup T` or `S \ T` is an error there.
`Any` is the set of every value; it prints as `ANY`. `TLCSet(i, v)`, for
a natural number `i` or a string `i` that begins with `s:`, keeps `v` in
register `i` and yields `TRUE`; `TLCGet(i)` yields it, and is an error
when nothing was kept; `TLCGet("all")` is the function from each
numbered register to the tuple of its value in each of TLC's workers,
`TLCGet("all:named")` the same of the named ones, and a tuple has one
value in Manyan, whose workers print what one does;
`TLCGet("-Dk")` is Java's system property `k`, the string `"-Dk"` when
unset, and `TLCSet("-Dk", v)` sets it to `v` as printed;
`TLCGet("level")` is the depth of the state a predicate is evaluated on
(of the step's first state in an action, its second's primed, 0 in Init
and the assumptions);
`TLCGet("config")` is the record `[mode |-> "bfs", deadlock |-> b, worker
|-> n, seed |-> s]` of a search, without TLC's fields naming its jar and its
fingerprint polynomial; of a simulation, with `mode |-> "simulate"`, it
also has `traces` (-1 without `num=`), `depth`, `aril |-> "0"` and `sched
|-> "random"`, and its assumptions find the search's counters undefined.
`TLCGet("distinct")`, `"queue"`, `"diameter"` and `"generated"` are the
search's counts of states found, queued, the depth reached and states
generated, each successor counted as it is checked; `TLCGet("stats")` is
the record of them with `initial`, the initial states generated,
`duration` and `worker |-> 0`.
`TLCGet("spec")` is the specification as TLC processed it: the records
of name and location of its initial predicates, of its actions as split
(§11.2, `TLCGet("action")`'s), of its fairness conjuncts, its invariants
and each `[]P` of its properties, the properties' other parts, its
variables and its constraints. A part with no definition is named
`UnnamedAction`, a property's part by the property, and one seen through
an instance that substitutes is located by the instance. TLC's coverage,
which `-coverage` adds to each, is left out. TLC implements `TLCGet` by an evaluation method, so
its errors carry that method's preamble (§11.3). That method's level is
1: a definition that uses `TLCGet` is not evaluated once as a constant,
but each time it is used, and a substitution `C <- d` of one is
evaluated as the model is read, an error there being that of a
non-constant substitution (§9). Before TLC's checker exists, which is
before the assumptions are checked, `TLCGet("level")` is 0 and the
search's counters, `"config"` and the registers are undefined.

`AssertError(err, exp)`, `err` a string literal, is whether evaluating
`exp` fails with the message `err`: the message as TLC prints it, without
its location, with the preambles of the standard operators inside `exp`
but none of those outside; Java's own exceptions are not caught.
`TLCCache(e, k)` of a constant `e` is `e`'s value, computed once for each
value of `k` and kept; of a state-level `e`, `k` is evaluated and then `e`
twice, as TLC's search keeps nothing in a state and its definition computes
`e` again (once in a simulation, which keeps it); of an action, `e`.
`TLCModelValue(s)` is the model value named by the string `s`.
`TLCGetOrDefault(i, d)` is register `i`, numbered or named, or `d` if
nothing is kept there.
`TLCGet`, `AssertError` and `TLCCache` are evaluation methods: they
evaluate their arguments themselves, inside their method, so an error
there carries the method's preamble.

## 9 Model configuration

### 9.1 Syntax

A configuration is a sequence of statements; `\*` and `(* *)` comments as
in §3.3. The keywords: `CONSTANT` is followed by assignments; `INIT`,
`NEXT`, `SPECIFICATION`, `SYMMETRY`, `VIEW`, `ALIAS`, `_PERIODIC`,
`_RL_REWARD` and `CHECK_DEADLOCK` by one name or value each, and may each
appear once; the others by any number of names. As in TLC, any token stands where a name is expected, and the
configuration is read before any module, so its errors come first, each
as TLC's `ConfigFileException` at the line it is found: a word that is not
a keyword where one is expected, a keyword repeated or followed by nothing, an assignment without
`=` or `<-`, a set without its `}`.

The statements are taken, as TLC takes them, in this order whatever their
order in the file: the constants, the invariants, the specification (or
`INIT` and `NEXT`), the properties, the constraints, the action
constraints; so an error in one is reported before what a later one
would print.

| Statement | Meaning |
|---|---|
| `CONSTANT`, `CONSTANTS` | `c = v` binds constant `c` to the value `v`; `c <- Op` replaces `c` by the definition `Op`; `d <- [M] Op` replaces the definition `d` of module `M` by `Op` of the root module, and `d = [M] v` gives it the value `v`; `c = c` binds `c` to the model value `c`; a definition `d = v` is the value `v`, its body never evaluated; lines `F(a, b) = v` give the operator `F` the value `v` at the arguments `a, b` (applied elsewhere, an error; lines of different arity, an error before the model is checked), as TLC's `OpRcdValue`, and a later `F = v` replaces them; a constant whose value is no operator, applied, is that value |
| `INIT`, `NEXT` | the initial predicate and next-state action |
| `SPECIFICATION` | a formula `Init /\ [][Next]_v /\ Fairness`, possibly through instances, `I(y)!Spec` too; with `INIT` or `NEXT` too, an error; a conjunct `[]S`, `S` an operator applied of constant or state level (not a number, string or `LET`), is an error naming `S` |
| `INVARIANT`, `INVARIANTS` | state predicates checked in every reachable state |
| `PROPERTY`, `PROPERTIES` | temporal formulas the specification must imply |
| `CONSTRAINT`, `CONSTRAINTS` | state predicates bounding the explored states |
| `ACTION_CONSTRAINT`, `ACTION_CONSTRAINTS` | actions bounding the explored transitions |
| `SYMMETRY` | a set of permutations of model values |
| `VIEW` | the expression whose value identifies states |
| `ALIAS` | the expression a trace's states are printed as (§11.2) |
| `CHECK_DEADLOCK` | `TRUE` (the default) or `FALSE` |
| `POSTCONDITION`, `POSTCONDITIONS` | constant formulas checked once the states are explored (§10.9) |

### 9.2 Values

A value in a configuration is a natural number, a string, `TRUE`,
`FALSE`, a model value (any other name), or a set `{v1, ..., vn}` of
values. As in TLC, `-1` is two tokens: the model value `-`, then a name. A model
value equals only itself.

## 10 Model checking

### 10.1 Constants

Each declared constant shall be bound by the configuration. Then the
assumptions are evaluated (§4.5).

### 10.2 Initial states

The initial predicate is evaluated as a generator: a conjunction is
evaluated left to right; a disjunction, an `\E`, an `IF`, or a `CASE` tries
each alternative; `P => Q` evaluates `P`, then continues with `Q` if it is
`TRUE` and without it if it is `FALSE`; `f[a]` for a lazy `f` (§6.6),
here only a recursive function or one over a domain not reducible, is
its body with its bound names given `a`; a conjunct `v = e` with `v` unassigned assigns `v`, and
`v \in S` with `v` unassigned assigns each element of `S` in turn; any
other formula must be `TRUE` for the alternative to continue. A state in
which some variable is unassigned is an error. Each state produced, once
the state constraints admit it, is an initial state.

### 10.3 Successor states

The next-state action is evaluated in a state `s` as the initial predicate
is, with primed variables `v'` in the place of variables, and unprimed
variables read from `s`. An action is split at its disjunctions, `\E`
quantifiers, and the definitions it refers to; `\E x \in S : A` is one
part if `S` is empty or fails to evaluate as it is split, and a call
`Op(a)` is one part, named `Op` and located at the call, if `Op` is built
in or an argument is not constant or fails to evaluate. Each part that produces a state is a transition. `UNCHANGED v` assigns `v'` the value of `v`. A
definition's parameter may stand for a primed variable, `Op(v')`, and a
constant operator for the definition that replaces it (§9.1); both are
followed. `f[a]`, for any lazy `f` (§6.6), is its body with its bound names
given `a`, so its disjunctions are alternatives and it may assign. A
successor in which some variable is unassigned is an error. `\A x \in S :
A` is the conjunction of `A` for each `x`, the first, then the others from
the last; as everywhere until every variable is assigned, each true
disjunct in it is a way to the successor, and each way counts as a state
generated.

### 10.4 Search

States are explored breadth first from the initial states, in the order
they are produced. A state is new when no explored state has the same
fingerprint: its value, or the value of the `VIEW` if one is given, up to
the group the `SYMMETRY` permutations generate (so `Permutations(A) \cup
Permutations(B)` relates the states either relates and their
compositions). TLC warns of a set of a symmetry that permutes nothing,
`Warning: The set S has been defined to be a symmetry set but contains less
than two elements.`, with `sets` and `have` for several, joined by `, and
`: it reads the arguments of the `SYMMETRY` definition's body, and names
all of them when they are as many as the permutations, else each
`Permutations(S)` of a constant set no model value of which a permutation
moves; a set is named by its text without spaces, or by the constant the
configuration replaces with it (`C <- S`). Each new state that satisfies the state
constraints, reached by a transition that satisfies the action constraints,
is checked against the invariants and queued. A reachable state with no
successor is a deadlock unless `CHECK_DEADLOCK` is `FALSE`.

The *states generated* count is the number of initial states produced plus
the number of transitions taken, duplicates included; *distinct states* is
the number of new states; the *depth* is the length of the longest shortest
path from an initial state, counted in states.

### 10.5 Properties

A `PROPERTY` holds when every behavior of the specification satisfies it.
A behavior is an infinite sequence of states, each transition of which is a
step of the next-state action or a stuttering step, that satisfies the
specification's fairness conditions: its `WF` and `SF` conjuncts and the
other temporal conjuncts, such as `<>[][A]_v`, which TLC checks as
conjuncts of the negated property. A property of the form `[]P` with `P`
a state predicate is checked as an invariant; a state predicate `P` is
checked on each initial state, after the invariants, as TLC checks it
while it computes them: `Error: Property P is violated by the initial
state:` and the state, with no counts (exit 13), or an error evaluating it
as one of an invariant there; `[][A]_v` is checked on
every transition; other properties are checked over the state graph after
the search (liveness checking). A property is split into its
conjuncts, following definitions and calls of an instance's definitions
without parameters (`I!Spec`), through any number of instances
(`Refinement == M!Spec` seen through `INSTANCE Mid`), and, outside
instances, `LET`, calls of a definition that is not recursive with
arguments (`I!P(a)` too), the arguments its parameters reach, and `\A x
\in S : P` over a constant `S`, a part for each `x` (no element is the
error `The liveness formula is a tautology.`). A parameter has the level
of its argument, and an operator parameter applied that of the operator
and of every argument. A part of several is named in messages by
its location, as `Invariant line 3, col 7 to line 3, col 15 of module M is
violated.`, the body of `\A` likewise, and a call's parts by the
definition called; `[]N`, with `N` a name without arguments (a
definition, constant, variable, parameter, `TRUE` or `FALSE`), is named
`N`. A state whose step violates an action property is not left on
the queue. In a temporal formula, `IF p THEN A ELSE
B` is `A` or `B` when `p` evaluates to a Boolean with no state (so a
`RECURSIVE` property can end), else `(p /\ A) \/ (~p /\ B)`. As TLC checks the negation of a property,
a constant in it is folded through `/\` and `\/`; `[]<>c` and `<>[]c`
joined at its top by them are checked with `c`'s value, but a constant
under any other `[]` or `<>` is in TLC's tableau, which never evaluates
it: `FALSE` there holds, so `<>TRUE \/ <>(x = 1)` is violated by a
behavior in which `x` is never 1. Liveness checking with a `CONSTRAINT` or
`ACTION_CONSTRAINT` prints TLC's warning, after the constant definitions
are evaluated and before the assumptions, `Warning: Declaring state
or action constraints during liveness checking is dangerous: …`, and with a
`SYMMETRY`, before it, `Warning: Declaring symmetry during liveness
checking is dangerous. …`; a simulation does not. Only the first warning of
a run is followed by `(Use the -nowarning option to disable this
warning.)`. A counterexample whose cycle is one state, with a step back to
it by any action, ends `State n: Stuttering`; in model checking, when a
conjunct of the property's negation (in disjunctive normal form) is
`<>[]A` or `[]<>A` with `A` no temporal formula, or a `<>F` in it has a
`[]` in `F`, TLC then warns that the stuttering may come of no
`SPECIFICATION` (with `INIT` and `NEXT`), or of a specification `Spec`
without fairness, `... the behavior specification Spec defined at line
..., col ... of module M. ...` (its whole definition). A counterexample
whose cycle comes back into the state it starts in after others ends
`Back to state i`, where TLC prints it stuttering, a behavior fairness
may rule out. A conjunct with an
action that is neither is TLC's `Error: Temporal formulas containing
actions must be of forms <>[]A or []<>A.` (exit 255). TLC builds the
tableaux as its checker starts, before the assumptions, evaluating the
constants in them: an error there is `Error: TLC threw an unexpected
exception.` with `java.lang.RuntimeException` and the message
(`tlc2.tool.EvalException` for a failed `Assert` and the errors TLC's
evaluator raises as such), with no counts (exit 255). As TLC, `[A]_v` and `<<A>>_v` in a temporal formula
test `v` first: a step that leaves `v` unchanged decides them, `A`
unevaluated.

TLC evaluates the predicates of the temporal properties during the
search, and an error there is reported then. On each initial state,
before its invariants, it evaluates the literals of each initial node of
a property's tableau, up to a false one, in the formula's order; it
evaluates nothing of a property without a tableau there. The first error is printed with `While working on the initial state:`
and the state, and the initial states are computed on; a second error
ends the search with its trace of positions (exit 75); without one, the
run stops once they are computed, without `Finished computing initial
states`, with the counts and exit 0, even after an invariant violation.
As it expands a state, it evaluates action predicates and fairness's
steps on each step to a successor and on the stuttering step, then
`ENABLED` predicates, fairness's enabledness and, for a property without
a tableau, the other state predicates on the state, then a tableau's
state predicates on each successor. An error there is an unexpected exception, with
the counts as the state is expanded and the depth (exit 255), or, for a
successor of `ENABLED` TLC cannot fingerprint, the trace alone. It comes
before an error or violation met expanding a later state. When Next
fails on a state on which an `ENABLED` predicate or one evaluated on the
state also fails, other than for a successor it cannot fingerprint, TLC
reports the error in Next with exit 255.

### 10.6 Fairness

`WF_v(A)`: a behavior in which `<<A>>_v` is eventually always enabled is
fair only if it takes infinitely many `<<A>>_v` steps. `SF_v(A)`: if
`<<A>>_v` is enabled infinitely often then infinitely many such steps.

### 10.7 Counterexamples

A trace is the shortest path from an initial state to the bad state. A
liveness counterexample is a path to a cycle (a lasso) on which the
property fails and the fairness conditions hold.

A property whose negation has a disjunct with no `<>[]A` or `[]<>A`
condition, checked without fairness, can fail on a finite path: one after
which the negation holds whatever follows. TLC builds the product of the
state graph and the negation's tableau as it expands each state, adding
the edges of the state's nodes, and at once those of each new node whose
state is expanded already. When such a node's tableau node has nothing
left to require, TLC stops the search there and reports the shortest path
to it, without its finite stuttering, as it reports an invariant
violation: the behavior ends at its last state, the counts are those of
that moment, and the exit status is 12. A path that ends at a state not
yet expanded is found when the search ends, as a lasso that stutters. A
deadlocked state is added after the deadlock is reported: a path ending
there is reported next, and the exit status is the deadlock's.

When several lassos qualify, TLC's choice is not specified (it can differ
between runs), so a conforming test admits exactly one.

### 10.8 Simulation

With `-simulate`, the checker explores random behaviors instead of the
state graph, as TLC does with one worker. `-seed S` (random if not given)
and `-aril A` choose the behaviors: the generator is Java's
`java.util.Random`, seeded with `S` and advanced `A` doubles, whose first
long seeds the generator that draws the behaviors. `RandomElement` and
the Randomization operators draw from two more, both seeded with `S`: one
for the model and the initial states, one for the behaviors. `num=N`
bounds the number of behaviors (unbounded if not given) and `-depth D`
their length in steps (100).

The initial states are computed and checked first, against the
invariants; a property that is a state predicate is not checked at all,
as TLC's simulation ignores it. Those outside the constraints are dropped,
then `Finished computing initial states: N distinct state generated.`
reports the rest (no state left is an error). Each behavior starts at one
of them drawn at random. In each state, an action (§10.3) is drawn at
random, then a prime from a fixed list of 1341, and the actions are tried
in steps of that prime until one has a successor in the constraints and
action constraints. Each successor is checked as it is generated, against
the invariants then the action properties, and one of those kept is
drawn as the next state. A behavior ends at its length, or at a state
with no successor kept, a deadlock unless `CHECK_DEADLOCK` is `FALSE`.
`TLCGet("diameter")` is the number of the behavior, from 1. A temporal
property is then checked on the
behavior, on a graph TLC builds as the states arrive. For a property
whose only temporal parts are `[]<>P` and `<>[]P`, as with fairness alone,
the graph has every state and step of the behavior, and every state may
also stutter. Otherwise TLC checks the property with a tableau, on its
product with the behavior: a node of the product, a state with a tableau
node, gets its successors when it is first met at a position of the
behavior, by the state stuttering or taking the behavior's next step there
(only stuttering at the last state), and keeps them; a later position of
the same state adds none. Which lasso is reported is not specified.

A violation prints the behavior up to the bad state, each state labeled
with the action it was taken by (the first by the last initial predicate:
a definition's name, else `Initial predicate`, and where it is written),
and the states equal to the one before them left out, compared variable
by variable from the end. Nothing is evaluated again. A successor that
leaves a variable unassigned prints as in model checking, with the
behavior to it, then the failure of TLC's postcondition that writes the
behavior out, and exits with status 75. An evaluation error prints TLC's
unexpected-exception report, but for an error TLC raises as a
`TLCRuntimeException`, one with a preamble of §11.3 or an undefined primed
variable, in a behavior: that prints as `Error:` and its message, then
the behavior, and exits with status 255 or 151; as the initial states are
computed it is a `java.lang.RuntimeException` (exit 255). With `-continue` a violation ends its
behavior and the simulation goes on, ending as if none was found.
`TLCSet("exit", TRUE)` ends the simulation after the step that sets it,
as if it were done. The
state counts of a simulation are unspecified (§11.1).

### 10.9 Postconditions

A `POSTCONDITION` is checked when the search or the simulation is done,
after the liveness checking, and after an error is reported: a violated
invariant, action property, property of an initial state, or temporal
property, a deadlock, or a successor not completely specified, once its
trace and the trace built again for it are printed (§11.2). The
postconditions are checked in order, each evaluated with no state, so
`TLCGet("level")` is 0 and a variable is undefined: the first that is
false prints `Error: Postcondition P at line ... of module M is false.`,
and the first that fails `Error: Evaluating postcondition P at line ... of
module M failed.` and the error, or that `TLC expected a boolean value,
but did not find one.` and its location; the rest are not checked. Each
name is resolved first: one the spec does not define as an operator, a
constant definition TLC evaluated at startup, or one with parameters, is
TLC's unexpected `java.lang.RuntimeException`, and no postcondition is
checked. After an error the exit status is the error's, and an error
resolving a name is ignored; else a false or failed postcondition replaces
`Model checking completed. No error has been found.`, before the counts,
with exit 10, and an error resolving one with exit 255. A simulation
reports an error resolving a name as `Error:` and its message, exit 151,
even after an error, whose status it replaces; after an initial state
that violates an invariant, it is followed by `While working on the
initial state:` and the state, exit 255.

## 11 Output

### 11.1 Normalized output

Normalized output is the standard output with these lines removed: the
version and start-up banner, `Parsing file`, `Semantic processing`,
`Starting...`, `Computing initial states...`, `Computed N initial
states...`, `Progress(...)`, `Checking temporal properties for`,
`Finished checking temporal properties`, `Implied-temporal checking`,
`Finished in`, a simulation's `Progress: N states checked.`, `The number
of states generated:` and `Simulation using seed`, the average outdegree, the fingerprint-collision report,
and the block that begins `Error: The error occurred when TLC was
evaluating the nested expressions`. Timestamps are removed from `Finished
computing initial states`, and runs of blank lines are one blank line.
When parsing or semantic analysis fails, the normalized output is the
single line `Error: Parsing or semantic analysis failed.`; the diagnostics
before it are unspecified. The exit status follows as a final line
`exit N`.

### 11.2 Results

Output printed by `Print` and `PrintT` while assumptions are checked comes
first. Then

```
Finished computing initial states: N distinct states generated.
```

or, when the initial predicate produced some state more than once,
`Finished computing initial states: G states generated, with N of them
distinct.`

and, for a correct model,

```
Model checking completed. No error has been found.
N states generated, M distinct states found, 0 states left on queue.
The depth of the complete state graph search is D.
```

A violation prints its error (§11.3), then, if there is a trace,
`Error: The behavior up to this point is:` and the trace, then the counts.
Each state of a trace is `State i: <Action line l1, col c1 to line l2, col
c2 of module M>` (`<Initial predicate>` for the first) followed by the
state as a junction list `/\ v = value` of its variables in TLC's order
(below), a single variable without the bullet, and a blank line. The action
is named by the definition the step's disjunct belongs to, with the
values of its constant arguments, `<Inc(1,2) ...>`, and located by that
disjunct. A definition seen through an instance that substitutes, as SANY
substitutes each declared name it does not, is one action, `I!A`, located
at the `INSTANCE` statement; a step of a specification's `[][N]_v` that
is no definition is `Action`, there too through such an instance. In a
simulation the initial predicate is named and located likewise.

With an `ALIAS`, each state of a trace, a counterexample, a simulated
behavior, or an initial state that violates an invariant or property is
printed as the alias's value on the step from it to the state after it,
the last state's to itself and a cycle's last to the state it goes back
to, with `TLCGet("level")` the state's number: a record is printed as the
state, its fields as variables in the order its constructor gives them,
any other value leaves the state as it is. TLC resolves the alias as it
prints a state, so an undefined name, a constant, or one with parameters
is, like an error evaluating it, printed as a variable `_ALIASEvalError`,
a string of the error's message, after the state's variables.

A record's field `_format`, a string, is the Java format each other field
is printed with, as `String.format(_format, name, value)` with the value
as TLC prints it: `%s` and `%S`, with the flag `-`, a width, a precision
and an argument index `n$`, `%b`, `%h`, `%n` and `%%`. Any other
conversion, or a third argument, is Java's exception, which ends the
trace before the state's number as an error building it does (below).

TLC builds a trace by evaluating Init, and Next from each state, until it
finds the state, so what they print is printed again as the trace is
printed. After a deadlock, a violated invariant or action property, or a
successor not completely specified, it builds the trace once more, for a
postconditions (§10.9), before the counts; so too after an error in Next on a state
with no successor generated before it, when deadlock is checked. An error
building a state ends the trace there, reported as `Error: TLC threw an
unexpected exception.` with `tlc2.tool.EvalException` and its message.

TLC's order of the variables is the reverse of the order in which SANY's
context of the root module, a `java.util.Hashtable`, enumerates them. The
table holds the names of SANY's 72 built-in operators, put in reverse
order of their definition, then the module's symbols in the order SANY
meets them: those of each extended module that are not LOCAL, in that
module's order; then, in the module's text, each declared or defined name,
the name of a RECURSIVE operator where it is declared, the name of a named
theorem or assumption, and the name of a nested module. An instance puts
the definitions of the instantiated module, then its named theorems and
assumptions, as that module's own table enumerates them; a named instance
`I` puts each as `I!Op`, its module instances too, then `I`. A name's hash
is Java's `String.hashCode`; the table starts with 11 buckets, puts a new
entry at the head of its bucket, and when it holds three quarters of its
capacity it grows to twice plus one, moving entries from the last bucket
to the first, each to the head of its new bucket. It enumerates the
buckets from the last to the first, each from its head.

A liveness counterexample is introduced by `Error: Temporal property P was
violated.` and `Error: The following behavior constitutes a
counter-example:`; it ends with `Back to state i: <Action ...>` when it
loops back to state `i`, or `State n: Stuttering` when it stutters forever.

### 11.3 Errors

| Situation | First line | Exit |
|---|---|---|
| assumption false | `Error: Assumption line l, col c to line l2, col c2 of module M is false.` | 10 |
| assumption fails to evaluate | `Error: Evaluating assumption line ... of module M failed.` | 10 |
| postcondition false, after the search | `Error: Postcondition P at line ... of module M is false.` | 10 |
| postcondition fails to evaluate, after the search | `Error: Evaluating postcondition P at line ... of module M failed.` | 10 |
| deadlock | `Error: Deadlock reached.` | 11 |
| invariant fails in an initial state | `Error: Invariant Inv is violated by the initial state:` | 12 |
| invariant fails | `Error: Invariant Inv is violated.` | 12 |
| action property | `Error: Action property P is violated.` | 13 |
| temporal property | `Error: Temporal property P was violated.`, P each PROPERTY the counterexample violates (`Temporal properties P and Q were violated.`) | 13 |
| `Assert` | `Error: The first argument of Assert evaluated to FALSE; the second argument was:` | 14 |
| successor not specified | `Error: Successor state is not completely specified by the next-state action. The following variable is not defined: v.`; with several actions, `by action A of the next-state relation` | 75 |
| invariant not Boolean | `Error: TLC expected a boolean value, but did not find one. ...` | 75 |
| constraint defined as a number or string | TLC's `ClassCastException`: `Error: class tla2sany.semantic.OpDefNode cannot be cast to class tlc2.value.impl.Value (...)`, then `While working on the initial state:` and the state | 75 |
| error evaluating an invariant in an initial state | the evaluation message, then `While working on the initial state:` and the state | 75 |
| error computing a function constructor in full (§6.6) | the evaluation message (and the trace, in an action), then `Error: TLC was unable to fingerprint.`, a blank line, `Fingerprint Stack Trace:`, TLC's call stack as it evaluates Init or Next again, outermost first, as `0. Line l1, column c1 to line l2, column c2 in M` (through an instance that substitutes, the `INSTANCE` statement after the call, the call left out for a part of the `SPECIFICATION`; `UNION {S}` with its set `{S}`), then the constructors entered within its innermost expression (without a call stack, the constructors being computed, innermost first, numbered down to `0) line l1, col c1 to line l2, col c2 of module M`), a blank line, `Reason:` and the message again | 75 |
| fingerprinting an initial state that holds a function over an infinite domain | `Attempted to compute the number of elements in the overridden value Nat.` (TLC's error counting the domain), then `While working on the initial state:` and the state | 75 |
| error evaluating a constraint or action constraint on a successor | `Error: TLC threw an unexpected exception.`, the evaluation message, and the trace to the successor | 75 |
| error fingerprinting a successor | `Error: TLC threw an unexpected exception.`, the message, the trace to the state, then, seeking the successor again by equality, the exception again for a value TLC has no fingerprint for (`Nat`), or TLC's `NullPointerException` for a set it cannot compare | 75 |
| error evaluating an invariant in a new state | `Error: Evaluating invariant Inv failed.`, the evaluation message, and the trace to the new state | 76 |
| other error evaluating an action | the evaluation message (below), with the trace to the state | 255 |
| no next-state action, and no invariant or property | `Finished computing initial states: ...`, then `Error: No next state actions defined to generate successor states from.` | 75 |
| a property part that is an action not under `[]` | `Error: The formula P at L is an action-level formula (i.e., it contains no temporal operators). ...`, the part named as properties are (§10.5), advising `[]` for `[A]_v`, `[]<>` for `<<A>>_v`, `[][A]_v` otherwise | 151 |
| the fairness and the negated properties' disjunction with more than 2^31 - 1 disjuncts in TLC's disjunctive normal form, which does not reach under temporal operators, an `SF` two and a `WF` one | `Error: TLC cannot handle the temporal formula because it exceeds the maximum supported size in disjunctive normal form.`, before checking | 255 |
| every temporal property's negation FALSE by its constants alone (`<>P \/ (1 = 1)`), `FALSE` folded through `/\`, `\/` and `<>` but not `[]`, in model checking | `Error: Temporal formula is a tautology (its negation is unsatisfiable).`, before checking | 77 |
| constant not assigned | `Error: The constant parameter K is not assigned a value by the configuration file.` | 151 |
| an invariant with primes or temporal operators, checked before the configuration's other names | `Error: The invariant Inv is not a state predicate (one with no primes or temporal operators).` | 76 |
| a constant invariant, property, constraint or action constraint, other than a literal, that is not `TRUE` (one that is is dropped); constant as TLC bounds levels, every argument of a call counting, used or not | `Error: The invariant of Inv is equal to v`, `property`, `constraint` or `action constraint` for the others | 151 |
| a temporal formula evaluated as a predicate or action | `Error: TLC encountered a temporal formula ([]A) when evaluating a predicate or action.`, the operator as `[]A`, `<>A`, `a ~> b`, `a -+-> formula`, `WF`, `SF`, `\EE` or `\AA` | 75 |
| action composition `A \cdot B` | `The current version of TLC does not support action composition.` | 75 |
| configuration names an undefined operator | `Error: The initial predicate Op specified in the configuration file` | 151 |
| parse or semantic error | `Error: Parsing or semantic analysis failed.` | 150 |
| a decimal in the spec (§3.5) | `Error: TLC can't handle real numbers.` and the decimal as written | 151 |
| a numeral above 2^31 - 1 (§3.5) | `Error: TLC can't handle a number this big.` and the numeral | 255 |
| a property TLC cannot check, such as `\EE x : F` or `\AA x : F` | `Error: TLC cannot handle the temporal formula` and its location, before checking | 255 |

The evaluation messages, as the line after `Error: Evaluating assumption`
or as the first line of an action error:

| Situation | Message |
|---|---|
| `a \div 0`, `a % 0` | `The second argument of \div is 0.` |
| `0 ^ 0` | `0^0 is undefined.` |
| result outside 32 bits | `Overflow when computing a+b` (the operator and operands) |
| `f[a]` outside `DOMAIN f` | `Attempted to apply function:` / `f` / `to argument a, which is not in the domain of the function.` |
| `t[i]` for a tuple `t` | `Attempted to apply tuple` / `t` / `to integer i which is out of domain.` |
| `r["f"]` for a record `r` | `Attempted to apply the record` / `r` / `to nonexistent record field f.` |
| `r.f` for a record `r` | `Attempted to select nonexistent field "f" from the record` / `r` / location |
| `f[a]` for a lazy `f` (§6.6) | `In applying the function` / `f,` / `the first argument is:` / `a` / `which is not in its domain.`; with several bounds, `the argument number k is:`, or `the argument list is:` and `which does not match its formal parameter.` when `a` is not a tuple. Where `f[a]` is part of an action or the initial predicate (§10.2), TLC binds `a` itself and reports a RuntimeException: `which` follows `a` on its line, but on the next for a tuple pattern among several bounds, the location of `f` follows, and an `a` that is no tuple for several bounds is `Attempted to apply a function to an argument not in its domain.` |
| `CHOOSE` with no witness | `Attempted to compute the value of an expression of form` / `CHOOSE x \in S: P, but no element of S satisfied P.` |
| `CASE` with no true guard | `Attempted to evaluate a CASE with no conditions true.` |
| `1 = "a"` | `Attempted to check equality of integer 1 with non-integer:` / `"a"` |
| `<<>> = {}` | `Attempted to check equality of the function << >> with the value:` / `{}` |
| a non-Boolean `/\` operand | `Attempted to evaluate an expression of form P /\ Q when P was` / `an integer.` |
| quantifier over `Nat` | `TLC encountered a non-enumerable quantifier bound` / `Nat.` |
| `+`, `-`, `*`, `\div`, `%`, `^`, `..` of a non-integer | `Cannot cast tlc2.value.impl.BoolValue to tlc2.value.impl.IntValue`, naming the class TLC keeps the value in |
| `x \in v` for a value `v` that is not a set | `Attempted to check if the value:` / `x` / `is an element of the integer 2` (or `the string`, `the boolean`, `the function`); for a tuple, `Attempted to check set membership in a tuple value.`; for a record, `Attempted to check if element:` / `x` / `is in the record:` / `v` |
| a value of the wrong kind in `Seq(S)`, `SUBSET S`, `[S -> T]`, `[a : S]`, `S \X T` | TLC's message for that set, such as `Attempted to check if non-record` / `x` / `is in the set of records:` / `S` |
| comparing `Nat`, `Int`, `STRING` or `Seq(S)` with another set | `Attempted to compare overridden value Nat with non-overridden value:` / `S` |
| enumerating or counting a set with an infinite part | TLC's message for the part, such as `Attempted to compute the number of elements in the overridden value Nat.` |

An error inside an operator of §8, which TLC implements in Java, such as
in the test of `SelectSeq`, follows a preamble for each such operator it is
inside, outermost first: `Attempted to apply the operator overridden by the
Java method` / its signature, as in `public static tlc2.value.impl.Value
tlc2.module.Sequences.SelectSeq(tlc2.value.impl.Value,tlc2.value.impl.Value),`
/ `but it produced the following error:`. The location of the inner error,
if any, ends the message. Errors that TLC raises as `EvalException`s, which
are those the operators of §8 raise about their own arguments, have no
preamble.

A message that names an expression is followed by its location, `line l,
col c to line l2, col c2 of module M`.

## 12 Exclusions

Not covered: the proof language (`PROOF`, steps, `USE`, `BY`; skipped,
except that a `HIDE` may name only theorems, assumptions, and steps, and a
theorem's statement is kept for §5.7), computing with real numbers and
with `\AA` and `\EE` (which TLC cannot either; §3.5, §11.3), `-generate`,
the configuration's `_PERIODIC`, `_RL_REWARD` and `_POSSIBLE` (rejected),
writing simulated behaviors to files (`-simulate file=`), simulation with
several workers, the order of `Print` output in a simulation, the order
of a record's fields in a simulated behavior (TLC's constructor order
until it compares or fingerprints the record), checkpointing, multiple workers' scheduling, distributed TLC, and the
TLA⁺ Toolbox outputs (`-tool`).
