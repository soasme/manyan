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
  `tests/fuzz.py live` makes on three seeds, each checked with the same
  random `-fp`, all print what TLC prints: Manyan orders a state's
  successors as TLC's table of them does, by TLC's fingerprints, and
  checks the properties as TLC does, by its possible error models. The
  rest: TLC's tableau is built of particles, its successors linked in the
  order of their index, so its product may have other nodes and edges
  than Manyan's.
- Model more of Manyan's algorithms in `tests/tla`, such as symmetry, and
  fuzz what the models cannot reach. The parallel search, the slicing of
  Init, the search for a fair cycle, the tableau, level checking and
  canonical formatting have models.

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
- Every expected output comes from TLC.
- With any number of workers, the output is identical to a one-worker run.
- An improvement over TLC that changes the output, such as a clearer error
  message, is opt-in. The default output stays TLC's.
