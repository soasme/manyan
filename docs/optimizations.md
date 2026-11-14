# Optimizations

What made Manyan fast, what was tried and gave nothing, and how to measure.
Each entry gives wall-clock seconds on the bench specs (arm64, best of 5)
before and after; [benchmark.md](benchmark.md) has the current comparison
with TLC.

## Measuring

- `bench/quick.sh [-workers N] OLD NEW`: the best of 5 runs of each engine
  on each bench spec, side by side. Compare binaries built from two
  commits, at the same time; nothing else may run meanwhile (a stray
  background job once hid a result).
- `sample PID 3 -file out.sample` on a build with `-O2 -g`, run on a model
  big enough to sample (counters with `Max = 8`: 4.78M states). Self
  samples point at the hot function; to split an inlined one, build a copy
  with `__attribute__((noinline))` on its parts.
- To count work instead of time, build a copy that counts `eval` calls by
  kind and arena allocations by caller (`__builtin_return_address`). For
  counters: 148 evaluations and 53 allocations per state expanded.
- `make bench` re-measures [benchmark.md](benchmark.md) against TLC with the
  profile-guided build; do it before a release.

## Kept

In the order they were made.

| change | effect |
|---|---|
| Fingerprints hash values directly, not their encoding; the encoding is made only for new states; a fingerprint slot keeps the state beside it | counters 2.34 → 1.63 |
| Standard-module operators of up to four arguments take them on the stack | (in the above) |
| Workers: forked processes expand wide levels over a shared store; the search merges in order, so output is that of one process | counters 1.62 → 0.58 with 8 |
| `sigsetjmp(.., 0)`: no signal-mask system calls per handler | (in the above) |
| A binding read from the current state keeps its value for the state's expansion | closure 284 → 1.12 |
| Workers claim a new state once: one invariant check per state, not per worker | duplicate work no longer grows with workers |
| Union of sorted sets merges; small sets sort by insertion; arrays the caller fills are not zeroed | closure 1.16 → 0.90, counters 1.66 → 1.48 |
| Workers merge each batch as it is done and find seen states themselves | counters 0.46 → 0.38 with 8 |
| Atoms and tuples compare without the general case | closure 0.86 → 0.83 |
| An argument that is a bound name with a fixed value binds the value, not a thunk; `x \in S` quantifies without a stack | closure 0.83 → 0.70, counters 1.27 → 1.18 |
| Fingerprints: an atom hashes inline | counters 1.18 → 1.15 |
| Fingerprints are sums of element hashes, kept by each set and function, so EXCEPT and Append update them by one term and decoding computes them | counters 1.15 → 1.04 |
| `eval` is an inline lookup in a table of one function per kind, so each call site has its own indirect branch to predict | closure 0.68 → 0.60, counters 1.04 → 0.88 |
| Set membership compares atoms and flat tuples inline in its binary search | closure 0.61 → 0.57 |
| EXCEPT looks its key up once, not three times | counters 0.88 → 0.86 |
| `-workers N` is N processes: the search expands a batch while it waits for one, instead of spinning | counters (4.78M states) 1.65 → 1.55 with 8 |
| Workers take room in the claim table 64 claims at a time, not one atomic add per claim | counters 0.28 → 0.23 with 8 |
| Profile-guided optimization (`make`), trained on the conformance suite (training on the bench specs instead gains about as much, so the suite is a fair profile) | clang: closure 0.55 → 0.48, counters 0.85 → 0.72, queue 0.18 → 0.16; gcc 15: counters 1.00 → 0.82 |
| An instance's substitution of state level, but a variable, is computed once per state, as TLC keeps a LazyValue | refinement with K = 8 2.09 → 1.55, counters (no instance) +1% |
| `<<x, y>> \in S`, of atoms and an enumerated S, probes S with the components, not a tuple made of them | closure 0.48 → 0.46 |
| A stored state's words are zigzag varints, a small number one byte | memory: PaxosCommit 2067 → 1140 MB, counters 188 → 145 MB; time: counters +3%, others under 1% |
| Two enumerated sets or tuples compare their atoms first, before `vcmp`'s checks for other kinds | partition with N = 10 1.25 → 1.15; tuples too: Examples' TLCSailfish1 9.95 → 9.65 |
| A native operator reached through an instance takes its arguments as values, without thunks, as `ev_call` does; a root module's call through instances without parameters keeps its `Inst` chain on the expression | Examples' Huang (1 worker) 66 → 46 → 43 |
| `r.f` keeps on the expression where the field was in the last record, and checks there first | Examples' MCPaxosSmall (1 worker) 20.3 → 18.6, 12% fewer instructions |
| Computing the initial states, the scratch arena takes regions: a quantifier's body and an initial state's invariants drop what they made, as constants do | Examples' MCBakery (655200 initial states) 2.14 → 1.93, 1.2 → 0.4 GB |
| A declaration keeps the index of its substitution by the module last instantiated, not searching the instance's substitutions at each read | instructions: Examples' AllocatorImplementation −3.6%, MCPaxosSmall −1.8% |
| A declaration read outside an instance skips the instance and ENABLED checks (a separate noinline function); a stored word under 64 writes one byte inline; `gen` does not expand a constant call | against 0.6.0's bench regressions: counters 2549 → 2510 M cycles, symmetry 621 → 606, log 173 → 165 |
| Workers compute the initial states: `Init`'s first choices split it into slices, numbered as one process takes them; each worker computes a batch of slices, skipping the others' alternatives, and the search merges them in order through the claims a level uses | Examples' MCBakery (4 workers) 1.33 → 0.73, its initial states 1.06 → 0.42 |
| A temporal property's action atoms are kept for each edge of the state graph, not evaluated again for each tableau node and each pass over the product | Examples' AllocatorImplementation 1.34 → 0.99 (1 worker), 1.11 → 0.76 (4); its atoms were evaluated 32 times an edge |
| With workers, a property's action atoms are evaluated on every edge in parallel before its check; one that fails, prints or draws is left to the check. Not for a property of state atoms alone: forking and decoding each state costs more than the check spends on them | Examples' AllocatorImplementation 0.75 → 0.52 (4 workers), 0.85 → 0.69 (2), and 0.65 (4) before an atom `~A` shared `A`'s value, which it evaluated twice; the quick bench's liveness, ten properties of state atoms, 0.16 → 0.24 before that exception |
| The scratch arena takes regions through the whole search, and a filter's test is one; a region keeps one chunk it drops for the next | Examples' MCInnerSerial: over 4 GB → 0.47 GB, 310 s (TLC 354 s); closure 0.51 → 0.53 s (plain -O2), the rest flat |
| An argument's value is kept while an initial state's invariants are checked, as for any other state: only a read of the initial state being found changes | tests/tla/MCInitSlices with 5552 initial states (a recursive operator passing its accumulator) 24.5 → 0.61; each `force` evaluated its thunk again, and that its argument's, down the recursion |

## Tried and dropped

| idea | why not |
|---|---|
| A fast path for `K_DECL` in `eval` | no gain; unsafe for a constant whose `var_index` is 0 |
| Fingerprint table split into fingerprints and states | no gain |
| A wrapper evaluating leaves without the dispatch | slower |
| `-fno-stack-protector` | about 2%, not worth a build flag |
| `veq` comparing two atoms of one kind first, as `vcmp` does | 2% fewer instructions on MCPaxosSmall, but 1% slower with the profile-guided build |
| `eval` as a switch calling one noinline function per kind | 2%; the table above does better |
| A tuple's value array in the same allocation as the tuple | no measurable gain |
| Prefetching fingerprint slots, successors queued 8 deep | none, slightly slower: the out-of-order core already overlaps the miss |
| Interning strings and model values (counters made 5.8M model values) | no gain: arena allocation is a pointer bump, and the scratch arena is reset each state, so it stays in cache |
| `t \in [1..n -> R]` for a tuple `t` checking the domain by the interval's bounds, without enumerating it | 0.25% fewer instructions on Examples' MCBakery, whose TypeOK does it twice per state: the profile's samples there were the members' checks |
| `assignable` with a fast path, an inline front, or a switch | each made partition about 11% slower with the profile-guided build; the loop form stays |
| `ev_call` computing `+ - < <= > >=` of two integers inline, without the native call | none on the quick bench with the profile-guided build (counters 0.78 → 0.77, others equal): the natives are a few instructions already |

## Where the time goes now

Counters, one worker: about 60% evaluating (148 tree nodes per state at
about 7 ns each), 35% keeping states (fingerprint lookup 16%, encoding,
records), 6% decoding. Closure: a third in set membership of tuples. Two
workers reach 1.6x one; the parallel path costs about 20% more work (claims,
encoding twice, a second lookup when merging).

The next large step for evaluation is fewer, cheaper nodes: resolving names
to slots, and fusing common shapes (`f[x]` with `f` a variable and `x` a
bound name, comparisons of integers) at resolve time.

## Open: where TLC gains more from workers

Examples' models where Manyan is least ahead of TLC (4 workers each) are
ones with a large serial part, not a slow evaluator.

- **AllocatorImplementation** (TLC 3.44 s, Manyan 1.38 s; Manyan 1.32 s with
  one worker). Its property `SchedAllocator` is checked on the state
  graph after the search, in one process: about half the samples are in
  `scc_search`, evaluating `[Sched!Next]_vars` on each of 64414 edges
  and the fairness `ENABLED`s of `Sched!Liveness` on each state. TLC
  evaluates these as each worker expands a state (`LiveCheck.addNextState`).
  Kept for each edge, the atoms are now evaluated once an edge, not 32
  times (above), and the workers evaluate them before the check, each
  on the edges of its states: 0.75 → 0.52 s with 4 workers. Left in one
  process are the 115 fairness conditions on each state and edge: the
  check makes 570424 `ENABLED` evaluations, 468217 of them distinct, and
  315589 steps, all distinct, of the 2.0 million and 7.4 million there
  are. Evaluating all of them in the workers would be about four times
  the work, so it would take components checked in parallel, not a
  fill.
  `subst_index` (above) took 3.6% off the evaluation itself.
  Since 0.11.0 a property is checked by its possible error models (PEMs),
  searched lazily, one at a time; filling every atom of every step in the
  workers first doubled the time with 4 workers (0.48 → 0.96 s). Instead
  the workers each search error models of the product, filling the shared
  atom cache as they go, and the search goes on in order from what they
  found: 0.48 → 0.24 s with 4 workers, 0.46 → 0.21 s with 8.
  Each search still took the `<>[]` conditions of its error model on
  every edge itself, 60% of its evaluations, and 7 error models make two
  rounds on 4 workers. The workers now evaluate those first, by state:
  0.25 → 0.22 s with 4 workers, 0.22 → 0.20 s with 8. Not where the
  offers (below) took them already, nor for a group of one error model,
  nor of state atoms alone: forking costs more there (EWD840 0.006 → 0.009 s,
  the quick bench's liveness +53% with 8 workers).
- **ReadersWriters, MCLiveWriteThroughCache.** A product of more than 8
  error models first computes what each component offers them, on one
  process: 0.25 s of ReadersWriters' 0.29 s with 4 workers. The
  components are found first, by a search that evaluates nothing, and
  the workers evaluate the offers' conditions in them, by state:
  ReadersWriters 0.25 → 0.12 s, MCLiveWriteThroughCache 0.19 → 0.09 s
  with 4 workers. Only above 100000 evaluations: below, the fork costs
  more (ElevatorLivenessMedium +26%, LiveHourClock +43%).
