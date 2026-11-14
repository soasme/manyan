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
- Follow new TLC releases. For each one, re-pin
  the oracle and re-bless the tests that changed.
- Give TLC's counterexample to a temporal property. Of 900 random graphs
  `tests/fuzz.py live` makes on three seeds, the verdict is TLC's on all,
  the counterexample one TLC prints on 897. Manyan now orders a state's
  successors as TLC's table of them does, by its own fingerprints in
  place of TLC's random polynomial, and checks the properties as TLC
  does, by its possible error models. The rest: TLC's tableau is built of
  particles, its successors linked in the order of their index, so its
  product has other nodes and edges than Manyan's.
- Model more of Manyan's algorithms in `tests/tla`, such as symmetry, and
  fuzz what the models cannot reach. The parallel search, the slicing of
  Init, the search for a fair cycle and the tableau have models.

## 2. Fast where TLC is slow

- Most specs are small or medium and get checked again after every edit.
  They should finish in milliseconds, fast enough to check on save, in a
  pre-commit hook or in CI.
- Large models should fit in less memory per state. A state set kept on disk
  would allow state spaces larger than RAM.
- Checking should scale with cores, liveness checking included.
- Before any speedup is kept, `docs/benchmark.md` must show it and show no
  regression elsewhere.

## 3. Embeddable

- Make `manyan.h` a stable C API: load a spec, check it, and walk the result
  without parsing printed text.
- Build bindings on that API: Python first, then an editor or language
  server integration.
- Compile Manyan to WebAssembly for a browser playground, where anyone can paste
  a spec and check it with nothing installed.

## Next: 0.12.0

In the order of the goals above. 0.11.0 brought liveness counterexamples to
TLC's on 897 of 900 random graphs, and 172 of the 176 Examples checked to
TLC's output; the other four are explained in [fullbench](fullbench.md).

1. **Fewer, cheaper nodes in evaluation.** Counters spends about 60% of
   its time evaluating, about 148 tree nodes per state
   ([optimizations](optimizations.md#where-the-time-goes-now)). Resolve
   variables and bound names to slots before the search, and fuse common
   shapes into one node. This speeds up every spec, and it should win
   back the 1–3% that `assignable`'s search for names cost log, recursion
   and symmetry in 0.6.1, and the 2–4% that the search's regions cost
   closure in 0.7.0. Done: integer comparisons and arithmetic, and `x[k]`
   of a variable (refinement and recursion 7%, counters 5%). Slots for
   bound names are not worth it: a lookup takes 1.0 to 1.7 steps of the
   environment on the bench (at most 3), and handling one without a call
   moved partition +4% in cycles.
2. **The serial part left with workers**
   ([optimizations](optimizations.md#open-where-tlc-gains-more-from-workers)):
   evaluate a property's fairness on the states and edges in parallel,
   not in one process (AllocatorImplementation). The initial states and
   a property's actions are computed in parallel already. Done for a
   property's error models, which the workers search: AllocatorImplementation
   0.48 → 0.24 s with 4 workers. Left: one error model's search, and the
   product it searches, built by one process.

## What stays

- The core language in one C file and one header, and the operators TLC
  computes in Java in another pair, on the core's API; no dependencies.
- Every expected output comes from TLC.
- With any number of workers, the output is identical to a one-worker run.
- An improvement over TLC that changes the output, such as a clearer error
  message, is opt-in. The default output stays TLC's.
