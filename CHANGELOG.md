unreleased:

- experimental: `-typecheck` checks a module's types as Apalache's
  `apalache-mc typecheck` (Snowcat) does: `@type` and `@typeAlias`
  annotations, inference with records, variants and rows, Apalache's
  messages and exit statuses. All 75 of Apalache 0.63.0's type checking
  tests give its outcome (tests/typecheck/apalache, ported by
  tests/apalache_port.py), and of all 62 annotated modules of
  tlaplus/Examples
- `-symbolic` makes Apalache's `Gen(n)` from the types `-typecheck` infers:
  Bug2973 and Bug3158 of Apalache's tests now run, and 182 of them give its
  outcome
- `-symbolic` refuses what Apalache refuses: a type error, a recursive
  operator or function, a set or `<<>>` of an open type, a `Repeat` of no
  literal count, a constant configured with a value not of its type, a
  set of sets of functions it would expand, a `LET` definition of an
  extended module named as a variable of the root, a disjunct that assigns
  other variables than its siblings; 33 more of Apalache's tests,
  those it refuses, give its outcome
- `-symbolic -max-error N` finds up to N violations told apart by the
  configuration's `VIEW`, as Apalache's `--max-error` with `--view`; its
  View, View2 and Test1305 tests give its count of errors
- `-symbolic` checks temporal properties under the specification's weak
  and strong fairness, as TLC does: a counterexample is a fair lasso, or
  one stuttering forever at its last state
- `-symbolic` checks `CONSTRAINT` and `ACTION_CONSTRAINT` as TLC does:
  a state outside them has its invariants checked but is not expanded
- `-symbolic` checks `ENABLED` in an invariant, a property or an action
  as TLC does; with a property under fairness, or constraints, a deadlock is TLC's, a state
  without a successor in any behavior, and a property is reported only
  once no invariant is violated and no state deadlocks
- `-symbolic` exits with TLC's 11 for a deadlock, and prints an invariant
  an initial state violates as TLC does
- `-symbolic` makes `Gen` of strings, uninterpreted types and variants,
  as Apalache does: a string the specification has or a fresh one
- `-symbolic` makes `Gen` in an operator whose parameters leave its type
  open, of the type each call instantiates
- a counterexample prints a state once where it moves only between the
  property's tableau nodes, as TLC does; it printed the state again, as
  an `<Initial predicate>` or a step to itself
- `tests/fuzz.py live` (`make fuzz-live`) checks random temporal
  properties of random state graphs under weak and strong fairness
  against TLC, with ten of its fingerprint polynomials, as the lasso TLC
  picks of several follows its fingerprints: of 900, on three seeds, all
  verdicts and 899 counterexamples are TLC's (before nested properties)
- `{x \in SUBSET S : P}` and `{f \in [D -> R] : P}` take each element in
  turn, as TLC does, keeping only those that pass, so `S` may have more
  than 24 elements and `[D -> R]` more than 100 million: Examples' SpanTreeTest5Nodes, a filter
  of the 2^32 sets of edges of five nodes, gives TLC's result (TLC 590 s,
  Manyan 168 s); it failed with an overflow
- a simulated counterexample that stutters at its end steps by no
  action in `CounterExample`, TLC's `UnnamedAction`, as TLC's simulator
  makes it
- a simulation checks the initial states' invariants as the search
  does, in the scratch arena: a record made there is written by `ToJson`
  in the order it was written, as TLC writes it
- an arena's memory is aligned for a 128-bit integer: `-generate`'s
  random order of a set's elements was stored misaligned (found by
  `make fuzz`)
- a simulated behavior's temporal properties are checked as TLC's
  simulator checks them (LiveCheck1): without its finite stuttering, on
  a product that steps on from the nodes new at each position only;
  `(x = 1) ~> (x = 2)` on a behavior that stays at `x = 1` is no
  violation then, as in TLC; with no fairness, its counterexample is
  the one TLC's search of that product (LiveCheck1) prints
- `tests/fuzz.py sim` runs a model that prints or asks one behavior
  only: TLC's worker goes on past an error until it is stopped, and what
  it prints then races
- a generated behavior's `Trace` writes each state's `_action` first in
  `ToJson`, as TLC's record of a state and its action holds it
- a counterexample's cycle ends with the step into its first state, as
  TLC's does; a move between that state's tableau nodes printed it twice,
  the last labelled `<Initial predicate>`
- `tests/fuzz.py live` checks nested temporal properties too; of 900 on
  three seeds, 896 counterexamples are TLC's
- `tests/tla/Tableau.tla` models the tableau: it accepts exactly the
  lassos a formula holds on, for the formulas of depth three over two
  predicates on every lasso of up to three states
- `[][]A` is `[]A` and `<><>A` is `<>A` in a temporal property, as TLC
  simplifies them: the counterexample to `<>[][]P` went around its cycle
  twice
- a temporal property whose negation has more than 64 eventualities
  `<>A` is checked right: their 65th shared the first's mark of being
  deferred, so a fair cycle that fulfils both at different states was
  missed. A tableau node defers `<>A` when it is among its next formulas
- a filter `{x \in U : P}` of a `UNION` TLC keeps tests the elements of
  its sets in turn, duplicates too, as TLC: it tested them sorted, so the
  states counted, the counterexample and an error of `P` could differ
- an error evaluating fairness is the one TLC reports first: weak
  fairness's `ENABLED` is evaluated with the actions on each step, before
  strong fairness's on the state
- `UNION S` of an `S` with an element that is not a set fails as TLC's
  does, "some element of s is nonenumerable"
- the counterexample to `<>[][A]_v` takes a step that is not `A`, as
  TLC's does; it could stutter, a behavior that satisfies the property,
  and named no property violated
- the counterexample to a property under strong fairness goes through a
  component TLC's search finds first: TLC checks SF_v(A) as A eventually
  never enabled, then as A taken infinitely often, so it stutters where A
  is disabled when it can; and as TLC, the cycle starts where the search
  entered the component, not at its node nearest an initial state
- a counterexample's cycle is built as TLC builds it: a walk from its first
  state that takes an edge meeting a fairness condition as soon as it sees
  one, then the shortest way back; it went by a shortest path to each
  condition in turn, through some states again and again
- a counterexample under weak fairness whose action is never taken goes
  through a state where it is disabled, as TLC's does; it stuttered at a
  state where it was enabled, a behavior that is not fair
- a temporal property's actions are evaluated once for each edge of the
  state graph: Examples' AllocatorImplementation 1.34 → 0.99 s
- tests/tla/Liveness.tla models the search for a fair cycle: on every
  product graph of three nodes, under weak and strong fairness, it finds
  a component exactly when there is a fair cycle, and the cycle it prints
  is fair
- tests/tla/InitSlices.tla models how workers slice Init: every Init of
  choices three deep gives its states in one process's order, sliced to
  each depth, one slice or two at a time
- an initial state's invariants keep the values of operator arguments, as
  every other state's do: a recursive operator with an accumulator, in an
  invariant of 5552 initial states, 24.5 → 0.6 s
- `-workers N` evaluates a temporal property's actions on the edges in
  parallel before its check: AllocatorImplementation 0.75 → 0.52 s with 4
- `-workers N` computes the initial states in parallel too, merged in
  the order one process finds them: Examples' MCBakery, 655200 initial
  states, 1.33 → 0.73 s with 4 workers
- `-symbolic` folds `ApaFoldSet` over a set not yet known as Apalache
  encodes it, where its definition's recursion did not end: Apalache's
  FoldSetInInit test runs (191 give its verdict)
- `-symbolic` reads Apalache's `OVERRIDE_X` definitions, for a constant or
  operator `X` the configuration gives none, and refuses a cycle they
  make, as Apalache does (its ConfigUnsorted test)
- `-symbolic` keeps an `\E` of more than 64 bindings in `Next` as one
  action, as Apalache does, where it split it into an action for each
  binding as TLC does: Apalache's factorization test, an `\E` over
  `2..1000000` twice, takes 0.02 s where it ran out of memory; Apalache's
  tests run with `--tuning-options` now run too (190 give its verdict)
- the configuration's `_PERIODIC`, evaluated as TLC does at a
  simulation's last progress report, and `_RL_REWARD`, checked and, as TLC
  does without its reinforcement learning, ignored
- the configuration's `_POSSIBLE`, as TLC 1.8.0 checks it: each state
  or action predicate it names must hold in some state or step of the
  model, or the run fails after the search with the counts TLC prints
- TLCExt's `PickSuccessor` asks on standard input whether to take a step,
  as TLC does
- `-symbolic -run-dir DIR` writes each counterexample in Apalache's ITF,
  as Apalache's `--run-dir` does: `violation1.itf.json`, ... and
  `violation.itf.json`, each value by its type
- CommunityModules' `Json` is built in, with its serializers as TLC's
  override writes them: `ToJson`, `ToJsonArray`, `ToJsonObject`,
  `JsonSerialize`, `ndJsonSerialize`
- TLCExt's `Trace`: the behavior to the state evaluated, in a search, a
  simulation, and an `ALIAS` while the error trace is printed
- TLCExt's `TLCEvalDefinition`: the body of the root module's definition
  of that name, as written; `TLCDefer`: TRUE, its expression evaluated
  when a simulation picks the successor it was met for
- TLCExt's `CounterExample` and `ToTrace`: in a postcondition after an
  error, the behavior TLC reports, its steps with their actions, a
  lasso's step back, and the `ALIAS`'s states where TLC gives them
- With `-continue`, an invariant or action property found violated is
  followed by no check of the postconditions, as in TLC
- An assumption of a level above constant is SANY's level error; an
  error raised in one of TLC's evaluation methods (`TLCEvalDefinition`,
  `TLCCache`, ...) is wrapped in its Java method, as TLC wraps it
- With `-continue`, an error evaluating a step is reported as TLC
  reports it: an error in Next is followed by the state's deadlock, or
  reported again as TLC replays it; one in an invariant or action
  property again as an error of the step. A `CounterExample` is
  `[action, state]` and Naturals' Java methods are its own, as TLC sets
  up no trace spec; so is a successor left incomplete, and a finite
  counterexample
- A property `WF_v(A)` or `SF_v(A)` under the specification's fairness
  gives TLC's fair counterexample, not one stuttering where the
  specification's fairness rules it out
- A successor left incomplete is followed by no check of the
  postconditions, as in TLC; manyan crashed on one using `CounterExample`
- With `-difftrace` and an `ALIAS`, the alias's fields that are unchanged
  are left out, as TLC leaves them out, but an error evaluating it
- With `-continue`, an alias failing to print the behavior to a violated
  invariant or action property fails the check and the step, as in TLC
- With `-continue`, a constraint failing on a successor, or a successor
  TLC cannot fingerprint, is reported again as TLC replays the step
- With `-continue`, an error in Init is followed by the initial states'
  violations again, as TLC replays Init; an error in a property's tableau
  on a state stuttering is found where TLC's search finds it
- With `-view` and `-difftrace`, a state after another is printed as what
  changed, as TLC prints it; with `-continue`, an initial state violating
  an invariant shown as the view is followed by no blank line
- With `-continue`, a deadlock followed by a postcondition TLC cannot
  resolve, or by a finite counterexample, is reported as TLC reports it,
  then again as TLC replays the step; an error in Next is reported again
  as first found
- With `-continue`, a check whose behavior fails to rebuild is an error of
  the step, which TLC replays and which may fail again, as TLC reports it
- In a simulation, `Trace` in an `ALIAS` is the behavior to the state
  printed, as in TLC
- `RandomElement` of a set TLC cannot enumerate, or of functions from or
  to one, fails as TLC fails; `-generate` counts the set it draws a
  successor from first, as TLC does
- With `-continue`, a simulation's `CounterExample` past an initial
  state is empty, as TLC's simulator keeps no behavior for it then
- An error checking the temporal properties of a simulated behavior is
  the one TLC meets first, as in model checking: weak fairness's
  `ENABLED` on each step before strong fairness's on the state
- The product graph of a temporal property is built in TLC's order, and
  each node takes its successors in TLC's order: as TLC's table of a
  state's successors holds them, by fingerprint, for a node there when
  its state is expanded; the stuttering step first, then the actions',
  for one added later. Counterexamples TLC could not print, such as a
  lasso stuttering where TLC's walk leaves the root, are gone
- `make fuzz-sim` also simulates with `-continue`
- `make fuzz-check` checks the models of tests/spec with random options,
  with Manyan (one or four workers) and with TLC

2026-11-12 0.10.0:

- experimental: `-symbolic` checks invariants and deadlock on behaviors of
  up to `-length` steps with a built-in SAT solver, as Apalache's
  `apalache-mc check` does, and replays each counterexample through the
  evaluator; `-cinit` chooses the constants the configuration leaves, as
  Apalache's `--cinit`, under the assumptions; an invariant with primes is
  an action invariant; Apalache's module is built in. 145 of Apalache
  0.63.0's own integration tests give its outcome (tests/symbolic/apalache,
  ported by tests/apalache_port.py), and the 46 models tlaplus/Examples
  checks with Apalache give its outcome, on average (geometric mean)
  hundreds of times as fast (docs/symbolic-bench.md)
- the test runners kill a run past a memory limit and run only as many at
  once as keep to half the machine's memory
- fix: a spec whose named instances grow the string table no longer
  crashes before any output (since 0.9.0; Paxos/MCPaxos, ewd998/EWD998ChanID)

2026-11-11 0.9.0:

- simulation: an alias whose _format Java cannot apply prints the behavior
  once (#1); a conjunct of Next that is no boolean is reported plainly, as
  TLC's TLCRuntimeException; TLCCache keeps a state's value in the state,
  an initial state's for every behavior from it
- no memory is lost once manyan_check returns: make sanitize checks it on
  Linux, and make sanitize-linux runs that in Docker; manyan_alloc gives a
  native memory that lives as values do

2026-11-10 0.8.0:

- renamed to Manyan (github.com/soasme/manyan): the command is manyan, the
  sources manyan.c, manyan.h, manyan-std.c and manyan-std.h, and the C API
  manyan_*, Manyan* and MANYAN_* in place of tpp_*, TPP* and TPP_*

2026-11-10 0.7.0:

- make full-bench checks tlaplus/Examples against TLC (docs/fullbench.md)
- tpp-std.c: the operators TLC computes in Java, on a public native API in
  tpp.h (tpp_define); CommunityModules' IOUtils, Json deserializers,
  Graphs, UndirectedGraphs, SequencesExt's SetToSeq and SVG (docs/std.md)
- action composition (\cdot, with -Dtlc2.tool.impl.Tool.cdot=true) and
  -Dk=v; fairness of the form <>[][A]_v and P => WF_v(A) with P constant
- under a VIEW, a property's actions are evaluated on the real steps; a
  property that is an instance's operator is named by the call
- the search drops what each quantifier's body and filter's test made
  (MCInnerSerial over 4 GB -> 0.47 GB), at 2-4% of the closure bench

2026-11-08 0.6.1:

- edge cases from tlaplus/Examples and TLC's own test models: instances,
  property splitting, ENABLED, configuration constants, tab columns,
  SUBSET and \subseteq, Bags, TLCGet and TLCSet, safety-like temporal
  properties, and TLC's message wherever a boolean, set or function is
  expected
- TLCExt: AssertError, AssertEq, TLCCache, TLCModelValue,
  TLCGetOrDefault, TLCNoOp, TLCGetAndSet; RealTime and Toolbox modules
- RandomSubset draws from up to 2^31 - 1 numbers without making the
  interval; Init draws on from the assumptions' generator
- a stored state takes one byte for a small number: half the memory for
  states of records (PaxosCommit 2.1 GB -> 1.1 GB)
- a state-level instance substitution is computed once per state
  (refinement bench 0.11 s -> 0.07 s)
- faster comparisons of sets and tuples, r.f, and standard operators
  through instances (Huang 66 s -> 43 s)
- computing initial states drops each candidate's garbage (MCBakery
  1.2 GB -> 0.4 GB)

2026-11-08 0.6.0:

- TLC 1.8.0 (d8fb231) is the oracle; every test is blessed by it, and
  tpp follows its messages, warnings, exit statuses, precedence, step
  labels, random draws and simulation
- ALIAS and POSTCONDITION

2026-11-07 0.5.1:

- make builds tpp profile-guided, 10 to 25% faster; make release removed
- builds without warnings under GCC 15
- examples/DieHard

2026-11-07 0.5.0:

- faster set operations, products, record and function sets, strings,
  constant sets and symmetry (partition 0.27 s -> 0.19 s, GameOfLife
  11.9 s -> 2.8 s, MCBakery 4.5 s -> 2.6 s)
- liveness checking takes 30% less memory and no longer leaks
- UNION S stays lazy as in TLC (MCDisruptor_MPMC now matches TLC)
- constant definitions and assumptions keep only their value
  (MCReachabilityTestAllGraphs 5 GB -> 3 MB)
- fixed: ENABLED recomputed constants, so a RandomElement could differ
- TLC's errors for infinite sets in states and fingerprint stack traces

2026-11-07 0.4.0:

- includes 0.3.0, never tagged
- -view, -userFile, -continue, -difftrace and -simulate file=FILE, also
  in the C API; -fp, -fpmem, -fpbits, -gzip and -cleanup are ignored
- random draws, TLCGet counters and simulation levels as TLC 2.19
- configuration checks, SANY's level rules and duplicate-definition
  warnings, as TLC and SANY
- edge cases from tlaplus/Examples and other public specs: lazy unions,
  recursive functions in actions, UNCHANGED through instances and
  parameters, VIEW with SYMMETRY, TLCSet("exit"), constant definitions
  as Init and Next
- tuples, sets, records, CASE arms and bound names of any number
- symmetry reduction 3x faster
- fixed undefined behavior found by the sanitizers on tlaplus/Examples
- tests/tla/Workers.tla models the parallel search

2026-11-06 0.2.0:

- -dump dot FILE, -nowarning; -metadir is ignored
- instances, the configuration, SYMMETRY and \A in actions as TLC treats
  them
- simulation checks temporal properties as TLC does
- Any, TLCSet, TLCGet
- more benchmarks: liveness, symmetry, partition, recursion, refinement

2026-11-06 0.1.0:

- first release: a TLA+ model checker that checks what TLC checks and
  prints what TLC 2.19 prints
- assumptions, invariants, action properties, deadlock and temporal
  properties under fairness; -workers N with one worker's output
- random simulation; TLC's error messages and exit statuses
- the C API (tpp.h)
- binaries for macOS, Linux and Windows (Cygwin; delete the bundled
  cygwin1.dll inside a Cygwin shell)
