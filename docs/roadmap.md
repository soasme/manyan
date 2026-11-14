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

## Next: 0.13.0

In the order of the goals above. 0.12.0 made evaluation faster
(refinement and recursion 7%, counters 5%) and moved liveness checking
with workers off one process (ReadersWriters and MCLiveWriteThroughCache
twice as fast with 4 workers); 172 of the 176 Examples checked give TLC's
output, and 897 of 900 random liveness graphs its counterexample.

1. **TLC's tableau.** The 3 of 900 counterexamples that differ come from
   TLC's tableau, built of particles and its successors linked in the
   order of their index, where Manyan's has other nodes
   ([manual](manual.md#limitations)). Build the tableau as TLC does, so
   that the product, and so the cycle found and the path to it, are
   TLC's: `tests/fuzz.py live` at 900 of 900.
2. **Nowhere slower than TLC.** Huang is the one model of the Examples
   where Manyan is slower than TLC: 41.0 s against 34.6 s with one worker
   ([fullbench](fullbench.md)). Find where its time goes, and then that
   of the next least ahead, MCInnerSerial (1.7x) and EWD998Small (2.2x).
3. **A result to walk.** `manyan_check` gives an exit status, and the rest
   is printed text. Give the C API the result itself: the verdict, the
   property or invariant violated, the counterexample's states, actions
   and loop, and the counts, as values `manyan.h` already reads. A
   binding needs it before anything else.

## What stays

- The core language in one C file and one header, and the operators TLC
  computes in Java in another pair, on the core's API; no dependencies.
- Every expected output comes from TLC.
- With any number of workers, the output is identical to a one-worker run.
- An improvement over TLC that changes the output, such as a clearer error
  message, is opt-in. The default output stays TLC's.
