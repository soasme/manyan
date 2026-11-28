# Roadmap

Manyan aims to be the TLC people run every day. It should give the same answers
and the same output, start instantly, need nothing installed, and be easy to
embed. It is not a new model checker with its own semantics, a proof checker
(TLAPS) or a symbolic one (Apalache).

The goals come in order. A later goal never costs an earlier one.

## 1. Same as TLC

Every other goal relies on people trusting a result from Manyan as much as one
from TLC.

- Run the specs of [tlaplus/Examples](https://github.com/tlaplus/Examples)
  against TLC (`make full-bench`), and publish how many give identical
  output ([full benchmark](fullbench.md)). Each spec that differs becomes a test in
  `tests/spec` and then a fix. The goal is all of them.
- The gaps the [manual](manual.md#limitations) lists by decision are
  left, each for the reason it gives; one is reopened when a
  specification needs it. Its known gaps are to be closed. The order of `Print` output in a simulation
  that stops early is TLC's threads' timing.
- Open, found by the fuzzers and not yet closed:
  - With `-dumpTrace`, a spec's own `POSTCONDITION` that prints
    `CounterExample` shows TLC's record `state` first, as TLC builds it,
    where Manyan prints it sorted, `action` first (the manual's
    limitation). Closing it means keeping a record in the order it was
    built until a field of it is read, as TLC normalizes then. It is
    most of what `fuzz-check` and `fuzz-sim` still report.
  - Where an error stops a simulation, the number of states generated
    can differ from TLC's (1 for 2; 10 for 5 with `num=4`). The runners
    ignore the line, so no test catches it.
  - `fuzz-check` draws neither `-metadir` nor `-gzip`.
- Follow new TLC releases. For each one, re-pin
  the oracle and re-bless the tests that changed.
- Give TLC's counterexample to a temporal property. Of 1500 random graphs
  `tests/fuzz.py live` makes on five seeds, each checked with the same
  random `-fp`, all print what TLC prints: Manyan orders a state's
  successors as TLC's table of them does, by TLC's fingerprints, checks
  the properties as TLC does, by its possible error models, and builds
  TLC's tableau of particles. A simulation searches its behavior as
  TLC's `LiveCheck1` does, and prints the lasso it finds where TLC
  prints the behavior's first states.
- Check Manyan against the semantics of TLA⁺, not only TLC: `make
  fuzz-prove` asks TLAPS to prove the value Manyan prints, `make
  fuzz-ref` compares it with `lean/`, a reference semantics in Lean 4,
  and `make fuzz-model` Manyan's verdicts, counts and traces; `lean/`
  proves that its computable oracle agrees with the classical one. Next:
  a proof that its evaluator respects `=` for values it keeps
  unevaluated (it is proved for the rest; `make fuzz-ref` tests it with
  twins of each expression written otherwise).
- Model more of Manyan's algorithms in `tests/tla`, such as symmetry, and
  fuzz what the models cannot reach. The parallel search, the slicing of
  Init, the search for a fair cycle, the tableau, level checking and
  canonical formatting have models.

## 2. Fast where TLC is slow

- Most specs are small or medium and get checked again after every edit.
  They should finish in milliseconds, fast enough to check on save, in a
  pre-commit hook or in CI.
- Large models should fit in less memory per state, and state spaces
  larger than RAM should check at disk speed. `-metadir` (after 0.18.0)
  maps the store of states and their records from files. In a Linux
  container without swap, PaxosCommit (1.32M states, 149 MB in memory)
  is killed under 100 MB without it; with it, it checks under 100 MB in
  55 s, as fast as without a cap, under 50 MB in 506 s, and under 30 MB
  it thrashes until killed after 46 minutes. What stays in memory, and
  what makes it thrash:
  - The fingerprint set holds each state's index, not its fingerprint:
    each lookup reads the state's record, at random in its file.
    TLC's `DiskFPSet` keeps the fingerprints, a bounded table in memory
    and a sorted file it searches with about one read per lookup.
  - Every state found is kept, encoded, for traces and liveness. TLC
    keeps only the states still to expand (`DiskStateQueue`), and for a
    trace a file of each state's fingerprint and predecessor
    (`TLCTrace`), from which it computes the states again.
  - A state's steps for liveness (`state_edges`) are in memory. TLC's
    `DiskGraph` keeps them in files, with an in-memory table from
    fingerprint to file offset.
  - Up to 2^29 states: the fingerprint set's slots are 30 bits.
  TLC's design is the one to follow: the same files, each a bounded
  buffer in memory. The first step is the fingerprint set; then the
  steps for liveness.
- Checking should scale with cores, liveness checking included.
- Before any speedup is kept, `docs/benchmark.md` must show it and show no
  regression elsewhere.

## 3. Embeddable

- Make `manyan.h` a stable C API: load a spec, check it, and walk the result
  without parsing printed text.
- Ship it where people install their tools: the executable on PyPI, a
  WebAssembly build on npm. Done in 0.14.0.
- Build bindings on that API: Python first, then an editor or language
  server integration.
- A browser playground, where anyone can paste a spec and check it with
  nothing installed. Done in 0.14.0.

## Next: 0.19.0

0.18.0 hardened what 0.17.0 had: the fixes for a red-team pass and
tlaplus/model-checker-hardening, and fuzzers that reach where those bugs
were (`fuzz-typecheck`, `fuzz-sym`, SANY oracles for `-fmt` and `-lint`,
richer values, models and temporal formulas). It agrees with TLC on all
2000 entries of a model-checker-hardening pbt campaign.

1. **Liveness on every core.** A property of state atoms alone is
   checked on one process, where forking the workers costs more than
   they save ([optimizations](optimizations.md)). Make more workers
   check it faster, its output unchanged.

## What stays

- The core language in one C file and one header, and the operators TLC
  computes in Java in another pair, on the core's API; no dependencies.
- Every expected output comes from TLC, unless TLA⁺'s semantics says
  TLC's verdict is wrong: then the semantics wins, and the manual says
  where. How a result is printed stays TLC's.
- With any number of workers, the output is identical to a one-worker run.
- An improvement over TLC that changes the output, such as a clearer error
  message, is opt-in. The default output stays TLC's.
