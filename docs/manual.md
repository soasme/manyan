# Manyan manual

Manyan checks TLA+ specifications the way TLC does: it reads a module and a
model configuration, explores every reachable state breadth-first, and
prints what TLC 1.8.0 prints. What Manyan accepts and what it must print are
defined by [the Manyan TLA+ Standard](standards/tla2.md); this manual covers
how to run it.

## Building

```sh
make            # builds ./manyan from manyan.c and manyan-std.c; needs a C11 compiler
make install    # installs bin/manyan and include/manyan.h, manyan-std.h under PREFIX (/usr/local)
```

`make` builds Manyan instrumented, runs the conformance suite with it, and
builds it again with the profile; the result is 10 to 25% faster than a
plain `-O2` build. It needs python3 to run the suite and, with clang,
`llvm-profdata` (Xcode has it); without them, it builds Manyan plain.

Manyan is one C file with no dependencies beyond the C library and POSIX
(`fork`, `mmap` for workers).

## Running

```sh
manyan [-config FILE] [-deadlock] [-workers N|auto] [-dump dot FILE] SPEC
manyan -simulate [num=N][,file=FILE] [-depth D] [-seed S] [-aril A] [-config FILE] [-deadlock] SPEC
manyan -generate [num=N][,file=FILE] [-depth D] [-seed S] [-aril A] [-config FILE] [-deadlock] SPEC
```

`SPEC` is the root module, with or without `.tla`. Modules it extends or
instantiates are read from the same directory; the standard modules
(Naturals, Integers, Reals, Sequences, FiniteSets, TLC, Bags,
Randomization, RealTime, Toolbox, TLCExt, Json) are built in. A module of
CommunityModules beside the spec gets the operators TLC computes in Java
for it; [std.md](std.md) lists them.

| option | meaning |
|---|---|
| `-config FILE` | the model configuration; `SPEC.cfg` by default |
| `-deadlock` | do not report deadlock, as TLC's `-deadlock` |
| `-workers N` | expand states with N processes; `auto` uses one per core |
| `-dump dot FILE` | write the state graph to `FILE.dot` (FILE if it ends in `.dot`) in Graphviz dot format, as TLC does, with one worker; `-dump dot,actionlabels FILE` labels each step with its action |
| `-simulate [num=N]` | check N random behaviors (no limit by default) instead of every state |
| `-generate` | simulate, building each successor by random choices instead of all of an action's successors, as TLC's `-generate`; takes `-simulate`'s `num=` and `file=` |
| `-simulate file=FILE` | also write each behavior that ends without an error to `FILE_0_N`, a module defining its states `STATE_1`, `STATE_2`, ..., each after a comment naming its action, as TLC does |
| `-depth D` | the length of each random behavior, in steps (100) |
| `-seed S`, `-aril A` | choose the random behaviors, as TLC's options do |
| `-symbolic` | experimental: check behaviors of up to `-length` steps with a SAT solver instead of enumerating states, as Apalache does (see [Symbolic checking](#symbolic-checking-experimental)) |
| `-length N` | symbolic checking: the steps in a behavior (10) |
| `-cinit C` | symbolic checking: the operator that chooses the constants the configuration leaves, as Apalache's `--cinit` |
| `-max-error N` | symbolic checking: the invariant violations to find (1), as Apalache's `--max-error`: those the configuration's `VIEW` tells apart |
| `-run-dir DIR` | symbolic checking: write each counterexample to `DIR` in ITF, as Apalache's `--run-dir` |
| `-typecheck` | experimental: check the module's types as Apalache's `apalache-mc typecheck` does, without a configuration (see [Type checking](#type-checking-experimental)) |
| `-version` | print the version and exit |
| `-nowarning` | turn off TLC's warnings, such as that of an EXCEPT outside the domain |
| `-continue` | go on after a violated invariant or action property, as TLC does: each new state's first violated invariant and each step's violated action property is reported, and the search ends with `No error has been found.`; a simulation ends the behavior and exits 255 at the end; one worker |
| `-view` | print each state an error reports as the value of the configuration's `VIEW`, as TLC does |
| `-Dk=v` | set Java's system property `k`, which `TLCGet("-Dk")` reads, as `java -Dk=v` does; `-Dtlc2.tool.impl.Tool.cdot=true` turns on TLC's incomplete action composition `A \cdot B` |
| `-stack N` | let expressions nest and definitions call at most N deep, and report TLC's `StackOverflowError` past that (exit 255 while parsing, 75 while evaluating); TLC's own depth depends on its Java stack. Without it calls go 5000 deep and parsing as deep as the C stack goes, so a spec nested far deeper crashes |
| `-userFile FILE` | write the output of `Print` and `PrintT` to FILE instead of standard output |
| `-difftrace` | print each state of a trace after the first as the variables that changed, as TLC does; the last state model checking reports is printed whole |
| `-inv EXPR` | also check `EXPR` as an invariant, after the configuration's, as TLC's `-inv`: an operator of the spec keeps its name, another expression is named `__DebuggerExpr__` and the time in milliseconds |
| `-invlevel N` | report the first behavior of N states, as TLC's: the invariant `TLCGet("level") < N` |
| `-postCondition M!Op` | also check `Op` of module `M` once the search is done, after the configuration's `POSTCONDITION`s; as TLC, the spec extends `M` |
| `-dumpTrace json FILE` | write the counterexample to FILE in TLC's JSON: its states, the actions between them and the variables, as `CounterExample` of TLCExt gives them |
| `-noGenerateSpecTE` | as TLC's: TLC then sets up no trace spec, which shows in the order of `CounterExample`'s fields |
| `-metadir DIR`, `-fp N`, `-fpmem F`, `-fpbits N`, `-gzip`, `-cleanup`, `-teSpecOutDir DIR`, `-lncheck WHEN` | accepted for TLC's command lines, and ignored: Manyan writes no metadata or trace spec, has its own fingerprints, and checks liveness once the states are found, as `-lncheck final` |
| `-h` | print the usage and exit |

A run prints TLC's report on standard output: the initial states, then
either `Model checking completed. No error has been found.` or the first
error with its trace, then the state counts and the depth of the search.
Manyan leaves out TLC's banner, timing and progress lines; everything else
matches TLC's text (Standard §11).

## Model configuration

The configuration file uses TLC's syntax (Standard §9):

```
CONSTANTS N = 3  Procs = {p1, p2}   \* p1, p2 become model values
INIT Init                           \* or SPECIFICATION Spec
NEXT Next
INVARIANT TypeOK Safe
PROPERTY Liveness
CONSTRAINT Bounded
ACTION_CONSTRAINT Steps
SYMMETRY Perms
VIEW Abstract
ALIAS Shown                         \* how a trace's states print
POSTCONDITION Done                  \* checked once the search is done
_POSSIBLE Reached                    \* must hold in some state or step
CHECK_DEADLOCK FALSE
```

`CONSTANT C <- Def` replaces a constant or operator by a definition, and
`CONSTANT D <- [M] Def` or `D = [M] v` a definition `D` of module `M`.
`SPECIFICATION` takes a
formula `Init /\ [][Next]_vars /\ Fairness`; its `WF_` and `SF_`
conjuncts, and others such as `<>[][A]_vars`, are the fairness assumptions
temporal properties are checked under.

## What is checked

- **Assumptions.** Each `ASSUME` must be true, or the run stops (exit 10).
- **Safety.** Every invariant holds in every reachable state (exit 12 with
  the shortest trace to a violation); every action property `[][A]_v`
  holds on every step.
- **Deadlock.** Each reachable state has a successor, unless deadlock
  checking is off (exit 11).
- **Liveness.** Temporal properties hold on every fair behavior, checked
  after the state graph is complete (exit 13 with a lasso-shaped
  counterexample).
- **Postconditions.** Each `POSTCONDITION` holds once the search is done,
  and each `_POSSIBLE` predicate held in some state, or step, of the
  model; TLC evaluates one only where the constraints hold (exit 10).
- **Evaluation errors.** An expression TLC cannot evaluate stops the run
  with TLC's message and location (exit 75, or 255 for errors TLC's
  standard-module operators report).

`Print`, `PrintT` and `Assert` behave as in TLC, including the extra
output TLC produces when it reconstructs a trace.

## Simulation

`-simulate` checks random behaviors instead of the whole state graph: from
an initial state drawn at random, it takes a random action's successors,
checks every one of them against the invariants and action properties,
and moves to one in the constraints at random, until the behavior has
taken `-depth` steps or stops (Standard §10.8). Temporal properties are
checked on each behavior as TLC's simulator checks them: without its
finite stuttering, on the product TLC builds from it, which follows only
the tableau nodes new at each state; a violation that needs another node
there is not found, as in TLC.
With the same `-seed` and `-aril`, Manyan draws the same behaviors as TLC
with one worker and prints the same report; `-workers` is ignored. A
seed is drawn at random unless one is given.

`-generate` simulates too, as TLC's `-generate` does, but builds one
successor at a time: within an action it tries a random disjunct, then
the others by a random prime step, and each `\E` binding and each value
of `x' \in S` or `x' \subseteq S` in TLC's random order, until a
successor is kept in the constraints. `TLCGet("config").mode` is
`"generate"`. As in TLC, a `CASE` in an action is an error.

## Symbolic checking (experimental)

`-symbolic` checks a specification the way Apalache's `apalache-mc check`
does: it unrolls `Init` and `-length` steps of `Next` into one formula,
encodes TLA⁺ values as bits, and asks a built-in SAT solver whether some
behavior that long violates an invariant or deadlocks. No state is
enumerated, so `x \in Int` or `x' \in x..(x + 100000)` costs a few
comparisons, not a state each. A counterexample is replayed through the
evaluator before it is printed, in TLC's format; one that does not replay
is reported as a bug.

It reads the configuration as Apalache does: `INIT`, `NEXT`,
`INVARIANT` (an invariant with primes is an action invariant, checked on
each step; an operator of one parameter is a trace invariant, checked of
each behavior so far, given as a sequence of records of the variables),
`PROPERTY` and `CONSTANT`. In `Init`, `x'` is `x`. `-cinit C` lets the operator `C` choose the
constants the configuration leaves, as `Init` chooses the variables, and
the assumptions then constrain that choice. As Apalache's, a definition
`OVERRIDE_X` stands for the constant or operator `X` the configuration
gives none, and a cycle such definitions make is refused. A constant `Init` or
invariant is checked like any other, and an expression the evaluator
fails on, such as `Head(<<>>)`, is some unknown value there, as in
Apalache. Apalache's own module is built in. Checked against Apalache
0.63.0: `make test-symbolic` runs 226 of Apalache's integration tests and
64 more, and `make full-bench-symbolic` the models tlaplus/Examples checks
with Apalache ([symbolic-bench](symbolic-bench.md)).

A temporal property is checked as Apalache checks one, on lassos: a
behavior of up to `-length` steps whose last state is one before it,
which then repeats forever. A behavior that never repeats a state is no
counterexample, and none stutters but as `Next` does. A violation is
printed as TLC prints one, ending with `Back to state N`.

Apalache has no fairness, constraints or `ENABLED`. With a property of a
specification with `WF_` or `SF_`, or with `CONSTRAINT` or
`ACTION_CONSTRAINT` in the configuration, the verdict is TLC's: a counterexample to a property is a
fair lasso, which may also stutter forever at its last state (`State N:
Stuttering`), and is reported only if no invariant is violated and no
state deadlocks in behaviors of up to `-length` steps; a deadlock is a
state without a successor in any behavior. A state outside the
constraints has its invariants checked, but no successors. `ENABLED A`,
in an invariant, a property or an action, is TLC's too: where the solver supposes
`A` disabled, it is asked again for a step of `A` from that state.

`-max-error N` goes on past a violation, as Apalache's `--max-error`
does, until N are found: each behavior after one must differ from it in
the configuration's `VIEW` of some state, so that the violations found
are as many as the views tell apart. Each is printed as TLC prints one.

`-run-dir DIR` also writes each counterexample in Apalache's Informal
Trace Format (ITF, its ADR-015), as Apalache writes it there:
`violationN.itf.json` for the Nth violation, `violation0.itf.json` for a
deadlock, and `violation.itf.json` for the last. Each value is written by
its type, and the constants are in each state. A lasso ends at the last
state before its loop, with `"loop"` the index of the first state on it;
Apalache instead repeats that state and adds its tableau's variables.
`vars` lists the variables as declared. Apalache's `.tla` and `.json`
counterexamples are not written.

As Apalache does, `-symbolic` refuses a specification that is not well
typed, a recursive operator or function, a set or `<<>>` whose type is
left open (`Cardinality({{}})`: annotate the empty set), a `Repeat`
whose count is no literal, and a constant the configuration gives a
value not of its type: a model value is a string, but `p_OF_PROC` a
`PROC`. It refuses, too, a disjunct, or an arm of `IF` or `CASE`, that
assigns other variables than its siblings: in `(x' = 1 \/ y' = 2) /\
x' = 1 /\ y' = 2`, TLC takes either disjunct, but Apalache finds which
`x' = e` or `x' \in S` assigns by the syntax alone, and needs each
disjunct to assign the same, and every variable assigned, even by an
action never enabled.

`Gen(n)` is any value of its type, with sets, functions and sequences of
up to `n` elements, as in Apalache: the specification is type checked
first, as `-typecheck` checks it, and each call makes another value, of
the type the operators it is called in are instantiated with there. A
string, or a value of an uninterpreted type `T`, is one the specification
has or a fresh one, `FRESHk` or `FRESHk_OF_T`, as Apalache makes them; a
variant is one of its tags.

Not supported, by decision: functions over an infinite domain, and
integers beyond 64 bits. A counterexample is replayed through the
evaluator, whose integers are 64 bits (TLC's are 32), and whose
functions are finite, as TLC's are; Apalache's own verdict on such a
function is wrong where it is tested (InfDomFun). [Apalache
gaps](apalache-gaps.md) tracks what Apalache does that `-symbolic` does not.

## Type checking (experimental)

`-typecheck` checks a module's types as Apalache's type checker, Snowcat,
does, and prints what it prints:

```
$ manyan -typecheck MC
Type checking MC.tla
 > Your types are purrfect!
Type checker [OK]
```

Every `CONSTANT` and `VARIABLE` needs a `@type:` annotation in the
comment before its name, and an operator may have one before its
definition. `@typeAlias: name = type;` names a type, and the old
upper-case aliases are read too. The rest is inferred: records and
variants with rows, tuples, sequences, functions, sets and operators,
polymorphic where nothing fixes a type. A type error names where it is
and each definition whose type could not be computed, and exits with 120;
a missing or unreadable annotation is a typing input error, and exits
with 255. Apalache's modules (`Apalache`, `Variants`, `Option`) and the
types it gives the standard and community modules are built in.

`make test-typecheck` runs Apalache 0.63.0's 75 type checking tests, each
with Apalache's outcome (`tests/typecheck/apalache`). Where several
`CONSTANT`s or `VARIABLE`s lack an annotation, Manyan names the one
Apalache names: a variable before a constant, the last in the order of
SANY's table of the root module's names.

## Exit statuses

| status | meaning |
|---:|---|
| 0 | no error |
| 10 | an assumption is false |
| 11 | deadlock |
| 12 | an invariant is violated |
| 13 | a temporal or action property is violated |
| 14 | an `Assert` failed |
| 75 | an evaluation error |
| 76 | an invariant is not a state predicate, or cannot be evaluated in a state the search reached |
| 77 | a temporal property is a tautology |
| 150 | the spec does not parse or fails semantic checks |
| 151 | the configuration names what the spec does not have, or a constant invariant that is not `TRUE` |
| 255 | another error, such as a configuration that does not parse |

## Workers

With `-workers N`, N processes expand states: Manyan forks N - 1 once the
search reaches a level of 256 states or more, and is the last itself. They
share the state store and the fingerprint set, read-only, and expand the
level in batches of 32 states; Manyan merges their successors in the order one
process would find them, and expands a batch while it waits for one. A state whose
expansion reports anything (an error, a violation, a deadlock, output from
`Print`) is expanded again by Manyan itself, so the output, including which
violation is reported and its trace, is the same for every N. Levels
smaller than 256 states are expanded by Manyan alone.

The initial states are computed by the workers too, when `Init` chooses
among enough alternatives (an element of `x \in S`, a disjunct, a
binding of `\E`): its first choices split it into slices, at least 32 for
each worker, which they compute and Manyan merges in order. An `Init`
that, down to those choices, fails, prints or draws a random element,
or a specification with temporal properties, is computed by Manyan alone;
so is a slice whose states report anything, in its turn.

## Library

`manyan.h` declares one entry point:

```c
#include "manyan.h"

ManyanOptions o = {.spec = "MySpec", .check_deadlock = 1, .workers = 1};
int status = manyan_check(&o);   /* prints the report; returns an exit status */
```

Compile `manyan.c` with `-DMANYAN_NO_MAIN` to link it into another program, with
`manyan-std.c` and a call of `manyan_std_init()` before `manyan_check` for the
operators of [std.md](std.md). `manyan_define` adds a native operator of your
own, as std.md shows.

## Testing

```sh
make test              # tests/spec with 1 and with 4 workers
make test-spec-oracle  # also runs TLC on every test (downloads tla2tools 1.8.0)
make bless ONLY=name   # writes a test's expected output from TLC
make sanitize          # tests/spec under UBSan (and Guard Malloc on macOS)
make fuzz              # mutated tests/spec models under the sanitizer build
make fuzz-oracle       # random expressions, printed by Manyan and by TLC
make fuzz-sim          # random simulations of tests/spec models, by Manyan and by TLC
make fuzz-check        # tests/spec models checked with random options, by Manyan and by TLC
make fuzz-live         # random temporal properties under fairness, by Manyan and by TLC
make bench             # times Manyan against TLC; writes docs/benchmark.md
make test-symbolic     # tests/symbolic with -symbolic
make test-symbolic-oracle  # also runs Apalache 0.63.0 on every test (downloads it)
make bless-symbolic ONLY=name  # writes a test's expected outcome from Apalache
make full-bench-symbolic  # tlaplus/Examples' Apalache models; writes docs/symbolic-bench.md
make test-typecheck    # tests/typecheck with -typecheck
make test-typecheck-oracle  # also runs Apalache 0.63.0 on every test
make bless-typecheck ONLY=name  # writes a test's expected outcome from Apalache
```

A test in `tests/symbolic` is a module and its configuration, as in
`tests/spec`, with an `options:` line for `-length`, `-deadlock` and
`-cinit`; `NAME.out` is Apalache's outcome (no error, the invariant
violated or a deadlock, with the length of the counterexample) and exit
status. With `NAME.itf.json`, `-run-dir` must write that counterexample. `tests/symbolic/apalache` is ported from Apalache's own
integration tests by `tests/apalache_port.py`. Each run is killed past
`--memory` MB resident (1000, 3000 with an oracle), and only as many run
at once as keep to half the machine's memory.

A test in `tests/typecheck` is `NAME.tla` with the modules it uses in
`NAME.files`; `NAME.out` is Apalache's outcome: `Type checker [OK]`,
`Type checker [FAILED]` with the definitions it could not type, or its
typing input error, then the exit status.

A test in `tests/spec` is `NAME.tla`: a module, then its configuration
after the line that ends the module. `NAME.out` is TLC's normalized
output and exit status. `tests/spec/tlc` holds models imported from TLC's
own test suite.

`make fuzz` swaps, drops or repeats one to three tokens of a random test's
model (most mutants still parse) and runs the sanitizer build on it, half
the time as a random simulation; it
must end with one of Manyan's exit statuses, without a signal or a sanitizer
report. A model that fails is kept as `.obj/crash-SEED-RUN.tla`.
`make fuzz-oracle` writes random constant expressions as `ASSUME
PrintT(e)` and checks that Manyan prints what TLC prints, narrowing a
difference to one expression. `make fuzz-sim` simulates random tests'
models with random seeds and depths, with Manyan and with TLC, one
behavior of a model that prints, asks or counts `_POSSIBLE` predicates:
TLC's worker goes on past an error until it is stopped. `make fuzz-check` checks random tests' models
with random options (`-deadlock`, `-continue`, `-difftrace`,
`-nowarning`, `-view`), Manyan with one or four workers. `make
fuzz-live` checks a random temporal property of a random state graph
under random weak and strong fairness, with Manyan and with TLC. All five take `RUNS=` (1000) and `SEED=` (1);
a run with a seed is repeatable. A case any of them finds becomes a test in
`tests/spec`.

## Limitations

Not supported, by decision, each for the reason given:

- the proof language: parsed and skipped, as TLC does.
- `-terse`: TLC prints a value as it builds it, an operator's body
  through SANY's own printing; Manyan builds its values first.
- `-maxSetSize`: Manyan does not bound the sets it builds, where TLC
  fails past 10^6 elements, an artifact of its Java arrays.
- `-dfid`: TLC's iterative deepening searches depth-first to a bound it
  raises, and finds a longer trace than breadth-first, which finds the
  shortest and checks the whole state space without a bound.
- `-coverage` and `-tool`: their output is TLC's cost model and its
  Toolbox's message codes, made for the Toolbox's views.
- `-generateSpecTE`, and the `_TTrace` module TLC writes at an error,
  which reads the trace from a `.bin` in Java's serialization; so too
  `-dumpTrace tlc` and `-loadTrace`. `-dumpTrace`'s other formats are
  written by CommunityModules' operators that Manyan does not have.
- checkpoints (`-checkpoint`, `-recover`) and distributed checking: TLC's
  files are its JVM's; models Manyan checks seldom run for the hours that
  call for them.
- the configuration's `_PERIODIC` is evaluated, as TLC does, at a
  simulation's last progress report; TLC evaluates it at its report each
  minute too, which Manyan does not print. `_RL_REWARD` is read only by
  TLC's reinforcement learning simulation, which a Java property turns
  on and which learns by TLC's fingerprints. `_POSSIBLE` is not read
  with `-symbolic`.
- TLC's fingerprints, and so TLCExt's `TLCFP` and the draws of
  `RandomElement`, `RandomSubset` and `RandomSetOfSubsets` in `Init` and
  `Next` when model checking, which TLC seeds with the state's
  fingerprint: TLC picks its fingerprint's polynomial at random on each
  run (`-fp` fixes it), so they change from run to run, and it
  fingerprints a model value by its index in SANY's table of names.
  Manyan's `TLCFP` stops the check, and it draws other values there.

`Trace` is the behavior to the state evaluated; to
rebuild it TLC evaluates `Init` again, and with more than one initial
state may give a shorter one. In a simulation
that stops at an error before its last behavior, TLC's worker goes on
with the next one while the behavior is printed, so its `Print` output
may come between the states; Manyan stops at the error. There a temporal
property is checked on the whole graph of each behavior, where TLC may
miss a counterexample of a property such as `P ~> Q`, or report another.
A simulated behavior prints each record with its fields in the standard
order; TLC prints a record in its constructor's order until it first
compares or fingerprints it, which it does as it goes. Real numbers
(`Reals`, decimals) and `\AA`/`\EE` give TLC's errors, as TLC cannot
check them either. `RandomElement`, `RandomSubset` and
`RandomSetOfSubsets` draw as TLC in a simulation, and in the assumptions
and constants when model checking.

Known gaps, not decisions, each to be closed:

- A temporal property's verdict is TLC's, but its counterexample may be
  another one TLC could print. TLC builds its tableau of particles, linked
  in the order of their index, and Manyan's tableau has other nodes, so
  where there is a tableau the cycle found or the path to it may differ.
  Where there is none, TLC's order of a state's successors comes from its
  random fingerprint polynomial, and Manyan takes its own fingerprints in
  its place: the counterexample is one TLC prints with some polynomial,
  not always one of those `-fp 0` to `-fp 9` give. Of 900 random graphs
  of `tests/fuzz.py live`, 897 print what TLC prints.
- `Print` and `PrintT` in a fairness condition or a temporal property
  print what Manyan evaluates, as its search needs each condition; TLC
  evaluates all of them on every state and step as it finds them, and
  prints each time.
- With `-noGenerateSpecTE`, an error in one of Naturals' operators TLC
  computes in Java names its class `Integers`, as without; TLC names
  `Naturals` until it reports a first error, and reads Integers then.
- Where TLC fails with a Java exception, hangs, or prints as a
  simulation's counterexample a lasso that does not violate the property,
  Manyan reports what the model does instead.
- Four of tlaplus/Examples print other output than TLC, for the reasons
  the [full benchmark](fullbench.md) gives.
- `-symbolic` and `-typecheck`: what Apalache does that they do not is in
  [Apalache gaps](apalache-gaps.md).
