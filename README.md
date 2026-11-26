# Manyan

<p align="center"><img src="docs/logo.jpg" alt="Manyan logo: a dragon and a koi in a circle" width="240"></p>

A fast model checker for TLA⁺, compatible with TLC and Apalache.

Website: [soasme.github.io/manyan](https://soasme.github.io/manyan/), with
the manual and a [playground](https://soasme.github.io/manyan/playground.html).

Manyan checks TLA⁺ specifications and model configurations with the same
semantics and default reporting behavior as TLC, and checks them
symbolically and type-checks them as Apalache does, without requiring a
JVM. It is an independent implementation written in C11, designed for fast
feedback, predictable results, and embedding in other tools.

Manyan does not extend the TLA⁺ language or fork TLC or Apalache. They are
its reference oracles: TLC 1.8.0 for model checking and simulation,
Apalache 0.63.0 for symbolic checking (`-symbolic`) and type checking
(`-typecheck`). Compatibility tests compare results, output, and exit
statuses against them.

**Naming:** Manyan (曼衍, *màn yǎn*, said "mahn-yen") comes from Zhuangzi's Qi Wu Lun (齐物论):
“和之以天倪，因之以曼衍.” It evokes continuous unfolding and transformation—a
fitting image for exploring the possible states of a system.

## Getting started

Each [release](https://github.com/soasme/manyan/releases) has `manyan`
built for macOS, Linux and Windows, and so does PyPI:

```sh
pip install manyan            # or uv tool install manyan
```

`npm install @soasme/manyan` is Manyan compiled to WebAssembly, for a web page or
Node.js; the [playground](https://soasme.github.io/manyan/playground.html) checks a spec
in your browser with it. To build it instead:

```sh
make                          # builds ./manyan; needs a C11 compiler
make install                  # install to your $PATH (/usr/local/bin)
```

To install into your current user workspace, run

```sh
make install PREFIX=~/.local  # installs ~/.local/bin/manyan
```

See [the manual](docs/manual.md) for the options, the configuration file,
exit statuses and the C API.

## Example Usage

Try it out:

```sh
$ manyan examples/DieHard
manyan version 0.18.0
Finished computing initial states: 1 distinct state generated.
Error: Invariant NotSolved is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ big = 0
/\ small = 0

State 2: <Next line 9, col 12 to line 9, col 37 of module DieHard>
/\ big = 5
/\ small = 0
...
```

To enable multi-worker mode:

```
manyan -workers auto examples/DieHard   # one worker per core
```

## Why Manyan?

**Compatible with TLC and Apalache.** Manyan accepts TLC-style TLA⁺ modules
and `.cfg` files. Its default output and exit statuses are tested against
TLC so it can be used in existing scripts and CI workflows. Some TLC
features are left out by decision; see [limitations](docs/manual.md#limitations).
`-symbolic` and `-typecheck` give the outcomes of Apalache's `check` and
`typecheck`, its counterexamples in ITF, and its type errors; what they
do not do yet is in [docs/apalache-gaps.md](docs/apalache-gaps.md).

**Fast startup and checking.** A small native executable avoids Java startup
overhead. Benchmarks on the included models show substantial speedups over
TLC, though performance depends on the specification and hardware.

**Deterministic parallel checking.** Use `-workers N` to explore states in
parallel. Manyan merges results in single-worker order, preserving the
reported violation and trace across worker counts.

**Small, embeddable implementation.** The checker is written in C11, with its
core in one file, `manyan.c`, and no runtime or dependencies. `manyan.h`
exposes it as a C API, and `manyan-std.c` adds the operators TLC computes in
Java, on that same API.

## Performance

Wall-clock seconds, best of 10 runs, on an Apple M2 (4 performance and 4
efficiency cores). TLC is tla2tools 1.8.0 (bc1b506). Every run prints the same
report as TLC with one worker.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.18 | 0.49 | 4.5x | 0.94 | 0.11 | 8.4x |
| counters | 823543 | 3.51 | 0.68 | 5.2x | 2.71 | 0.19 | 14.6x |
| liveness | 38880 | 4.29 | 0.14 | 30.1x | 2.91 | 0.07 | 40.2x |
| log | 31501 | 0.66 | 0.05 | 12.6x | 0.58 | 0.02 | 26.7x |
| mutex | 11365 | 0.47 | 0.03 | 15.3x | 0.43 | 0.02 | 24.5x |
| partition | 21147 | 0.92 | 0.18 | 5.2x | 0.71 | 0.06 | 12.8x |
| queue | 183680 | 0.96 | 0.16 | 5.8x | 0.87 | 0.06 | 15.0x |
| recursion | 78125 | 1.21 | 0.23 | 5.3x | 0.83 | 0.06 | 13.7x |
| refinement | 30618 | 0.64 | 0.07 | 9.1x | 0.54 | 0.02 | 22.2x |
| symmetry | 21123 | 1.21 | 0.18 | 6.7x | 0.68 | 0.05 | 13.8x |

`make bench` reproduces these numbers in [docs/benchmark.md](docs/benchmark.md);
[docs/optimizations.md](docs/optimizations.md) records how they were reached.

## What it supports

- The TLA⁺ language as TLC evaluates it: operators, functions, records,
  sequences, sets (including lazily evaluated infinite ones), `CHOOSE`,
  `LET`, recursion, `EXTENDS`, parameterized `INSTANCE`, nested modules,
  labels and subexpression names (`Op(a)!lab!:!2`), SANY's level checks.
- Standard modules: Naturals, Integers, Reals, Sequences, FiniteSets, TLC,
  Bags, Randomization, RealTime, Toolbox, Json, and TLCExt with `Trace` but
  its operators of counterexamples, fingerprints and interaction.
- Model configuration: `CONSTANT` values, model values and `<-`
  substitutions, `INIT`/`NEXT` or `SPECIFICATION`, `INVARIANT`,
  `PROPERTY`, `CONSTRAINT`, `ACTION_CONSTRAINT`, `SYMMETRY`, `VIEW`,
  `ALIAS`, `POSTCONDITION`, `CHECK_DEADLOCK`.
- Checking: assumptions, invariants, action properties, deadlock, and
  temporal properties under weak and strong fairness, with TLC's
  counterexamples; random simulation (`-simulate`, `-generate`), drawing
  the same behaviors as TLC for a seed, and writing them to files (`file=`);
  TLC's `-continue`, `-difftrace`, `-view`, `-userFile`, `-dump dot`,
  `-inv`, `-invlevel`, `-postCondition` and `-dumpTrace json`.
- TLC's error messages and exit statuses for evaluation errors, parse
  errors and configuration errors.
- Formatting and linting: `-fmt` formats a TLA⁺ module in one canonical
  layout while preserving comments, proofs and meaning; `-lint` runs
  SANY's syntax, semantic, level and warning checks without a model.
- Experimental: `-symbolic` checks invariants, temporal properties and
  deadlock on behaviors of up to `-length` steps with a SAT solver, as
  Apalache does, with its `--cinit` (`-cinit`), `--max-error`
  (`-max-error`, with the configuration's `VIEW`), `--run-dir` (`-run-dir`,
  counterexamples in ITF), action and trace invariants, `Gen` and its
  module, and TLC's fairness; 226 of
  Apalache's own tests give its outcome, refusing what it refuses, and so
  do all 46 tlaplus/Examples models checked with Apalache (see the
  [manual](docs/manual.md#symbolic-checking-experimental) and
  [docs/symbolic-bench.md](docs/symbolic-bench.md)).
- Experimental: `-typecheck` checks types and `@type` annotations as
  Apalache's type checker does; all 71 of Apalache's type checking tests
  give its outcome (see the
  [manual](docs/manual.md#type-checking-experimental)).

Left out by decision, each for a reason the
[manual](docs/manual.md#limitations) gives: TLC's `-terse`, `-maxSetSize`,
`-dfid`, `-coverage`, `-tool` and `-generateSpecTE`, checkpoints,
and distributed checking. Real numbers and `\AA`/`\EE`
give TLC's errors, as TLC cannot check them either. The proof language is
parsed and skipped.

## How it is tested

`manyan` follows [the Manyan TLA⁺ Standard](docs/standards/tla2.md),
with TLC 1.8.0 as the oracle for every choice the language leaves open,
and Apalache 0.63.0 for symbolic checking and type checking. The tests
follow it; they need python3, and those that run TLC or Apalache also need
Java (they download tla2tools 1.8.0 and Apalache 0.63.0 themselves):

- `tests/spec`: over 800 models, each with TLC's output and exit status.
  `make test-spec-oracle` runs TLC on every one of them as well, so a test
  can't drift from what TLC does. `tests/spec/tlc` holds models imported
  from TLC's own test suite.
- `make test` runs the suite with one worker and with four;
  `make sanitize` runs it under UndefinedBehaviorSanitizer (with Guard
  Malloc on macOS, AddressSanitizer elsewhere).
- `make fuzz` runs mutated models of the suite under the sanitizers, to
  find crashes; `make fuzz-oracle` compares what `manyan` and TLC print for
  random expressions, `make fuzz-sim` for random simulations of the
  suite's models, `make fuzz-check` for its models checked with random
  options, and `make fuzz-live` for random temporal properties
  under fairness, to find differences. What they find becomes a test.
- `tests/tla` models parts of `manyan`'s algorithms in TLA⁺, for TLC and `manyan` to
  check.
- `tests/symbolic`: 290 models for `-symbolic`, 226 of them from Apalache's
  own tests, each with Apalache 0.63.0's outcome; `make
  test-symbolic-oracle` runs Apalache on them too, so a test can't drift
  from what Apalache does.
- `tests/typecheck`: Apalache's 71 type checking tests for `-typecheck` and
  two of Manyan's, each with Apalache's outcome; `make
  test-typecheck-oracle` runs Apalache on them too.
- `make full-bench` checks tlaplus/Examples' models against TLC
  ([docs/fullbench.md](docs/fullbench.md)), and `make full-bench-symbolic`
  those it checks with Apalache against Apalache
  ([docs/symbolic-bench.md](docs/symbolic-bench.md)).

## Layout

```
manyan.c, manyan.h          the checker and its C API
manyan-std.c, manyan-std.h  the operators TLC computes in Java, on that API
docs/standards/             the language standard Manyan conforms to
docs/manual.md              how to use Manyan
docs/std.md                 the standard modules, and writing an operator in C
docs/benchmark.md           Manyan against TLC
docs/fullbench.md           tlaplus/Examples, Manyan against TLC
docs/symbolic-bench.md      tlaplus/Examples, -symbolic against Apalache
docs/apalache-gaps.md       what -symbolic does not do yet that Apalache does
docs/etcd.md                etcd's trace validation, Manyan against TLC
docs/optimizations.md       what made Manyan fast, and what did not
docs/roadmap.md             where Manyan is going
tests/spec/                 conformance tests, by chapter of the standard
tests/symbolic/, typecheck/ -symbolic's and -typecheck's tests, against Apalache
tests/tla/                  TLA⁺ models of Manyan's algorithms
examples/                   a spec and its configuration to try Manyan on
bench/                      benchmark specs, compare.py (against TLC), quick.sh (two builds)
CHANGELOG.md                what each release changed; releasing is tagging vX.Y.Z
```

## License

MIT; see [LICENSE](LICENSE). The Windows build ships Cygwin's
`cygwin1.dll`, which is LGPLv3.
