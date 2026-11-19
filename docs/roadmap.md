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
- Ship it where people install their tools: the executable on PyPI, a
  WebAssembly build on npm. Done in 0.14.0.
- Build bindings on that API: Python first, then an editor or language
  server integration.
- A browser playground, where anyone can paste a spec and check it with
  nothing installed. Done in 0.14.0.

## Next: 0.16.0

0.15.0 gave the result to walk: `ManyanOptions.result` in the C API,
`-result FILE` in JSON, `manyan.run` in Python and `run().result` in npm,
and the playground's counterexample state by state. A browser holds a
recursion 1,647 levels deep where it held 939, and the full bench covers
every model of tlaplus/Examples: 173 of 197 print what TLC prints, 27.6x
as fast.

1. **Large state spaces in less memory.** Six of the full bench's models
   hold more than its 4 GB in Manyan, where TLC keeps its fingerprints and
   behavior graph on disk: CoffeeCan3000Beans' 18 million transitions hold
   4.1 GB, where TLC checks it in a 2 GB heap, and DijkstraMutex's 33
   million states past 4 GB ([fullbench](fullbench.md#gaps)). Hold each
   state and transition in fewer bytes, and give those six a row.
2. **Faster.** Profile the bench's models and the full bench's slowest
   that print what TLC prints, and cut where the time goes;
   `docs/benchmark.md` shows each gain and no regression.
3. **A faster test suite.** `make test` runs tests/spec four times, with
   one and four workers, natively and for the result. Run it in less time
   without testing less.
4. **TLC re-pinned.** 1.8.0's jar is rebuilt under its tag; the oracle is
   now commit bc1b506 (TLCSet and TLCGet with several workers), every test
   blessed by it.

## What stays

- The core language in one C file and one header, and the operators TLC
  computes in Java in another pair, on the core's API; no dependencies.
- Every expected output comes from TLC.
- With any number of workers, the output is identical to a one-worker run.
- An improvement over TLC that changes the output, such as a clearer error
  message, is opt-in. The default output stays TLC's.
