# Full benchmark

`make full-bench` checks the models of
[tlaplus/Examples](https://github.com/tlaplus/Examples) with Manyan and with
TLC, and writes this report. `make bench` ([benchmark](benchmark.md)) is the
quick one for day-to-day work; this one takes hours and asks a stronger
question: does Manyan print what TLC prints on specs it was not written for?

Examples, CommunityModules and TLAPS are pinned in the Makefile. Each model
runs once with one worker, killed past 15 minutes (`TIMEOUT=` seconds), 4 GB
held, swapped out too, or once the disk has under 4 GB free, as TLC's states
spilled to disk can leave it. TLC's results are cached under `.obj`, a run
killed for time run again under a longer `TIMEOUT`, and the diffs of the
models that differ are written to `.obj/fullbench.diff`. `ONLY=DieHard` runs
the models whose path contains DieHard; `MAX_RUNTIME=00:00:30` keeps those
recorded to run in 30 seconds, and `MAX_RUNTIME=all` takes every model.

Of Examples' 243 models, the report below checks all 191 that TLC searches
exhaustively, with `MAX_RUNTIME=all TIMEOUT=3600`, and the 6 that simulate
or generate behaviors, fixed by `-seed 1` and `num=`; the other 46 are
Apalache's. Where TLC is killed, there is nothing to compare. Five differ,
for reasons Manyan keeps:

- ewd687a/EWD687a_anim: its ALIAS lays out its graph with SVG's
  `NodesOfDirectedMultiGraph`, which TLC computes with jungrapht's
  Sugiyama layout, a Java library's heuristics, and Manyan from its
  definition, a `CHOOSE` it cannot enumerate. Copying a layout library
  for one animation is not planned.
- SpanningTree/SpanTreeRandom draws its graph with `RandomElement` in a
  constant, which TLC draws anew each run, so its output is TLC's of one run.
- FiniteMonotonic/MCDistributedReplicatedLog: the same property is violated,
  but under its VIEW the two print different traces
  ([tlaplus#1045](https://github.com/tlaplus/tlaplus/issues/1045)).
- tower_of_hanoi/Hanoi.toolbox/Model_1/MC: TLC loads the model's own
  `Bits.class` and says so; Manyan computes `Bits!And` from its definition,
  with the same result.
- ewd998/SmokeEWD998_SC runs TLC itself, through `IOEnvExec` and the path
  `TLCGet("config").install` gives of TLC's jar, which Manyan has none of.

## Gaps

What the full bench does not compare, and what would close each gap.

| gap | models | to close |
|---|---:|---|
| TLC over an hour | 10 | A machine that runs TLC for longer, as the manifest records with more workers and memory |
| TLC fills the disk | 3 | A machine with more than 20 GB free for TLC's states |
| Manyan over 4 GB | 6 | Hold large state spaces and behavior graphs in less memory ([roadmap](roadmap.md#next-0160)) |
| more than one worker | 7 | Run those recorded over a minute with `-workers 4` too |
| symbolic | 46 | None: these are Apalache's models, not TLC's |

- TLC over an hour: CarTalkPuzzle Model_3 (it filters 121^5 functions),
  MCKVSSafetyLarge (recorded 7 h 16 min), EnvironmentController (2 h),
  SlushLarge (50 min), MCNanoLarge (20 min), MultiPaxos_MC, c1cs,
  TLCSailfish2, MC_HDiskSynod and EWD998ChanID_export.
- TLC fills the disk: bcastFolklore, BPConProof and EWD998ChanID_shiviz,
  their states spilled past the 4 GB floor after 1371, 2522 and 1489 s.
- Manyan over 4 GB: CoffeeCan3000Beans and DijkstraMutex
  Safety-4-processors, which the last report gave as the same as TLC's,
  hold over 4 GB, much of it compressed or swapped out: CoffeeCan3000Beans
  peaks at a 5.3 GB footprint, 1.05 GB of it resident, which the guard,
  counting only what is resident, let run. TLC keeps its fingerprints and
  behavior graph on disk. So too ElevatorSafetyLarge, aba_asyn_byz,
  EWD998 and TestMCReachability; the last violates a temporal property
  that TLC finds at its periodic check, each minute of the search, so the
  counts it prints are of when that check fell.
- More than one worker: the 167 models recorded to run in a minute or
  less were run once with `-workers 4` (by an engine wrapping
  `manyan -workers 4`): 160 print what TLC prints, as with one worker,
  and the four that differ with one worker differ alike; the run found
  TLCSailfish1's parse failure, since fixed. SlushMedium and
  MCBoulanger went past the 4 GB guard, which summed the resident memory
  of the worker processes, pages they share counted in each; it counts
  them once now, and run again with four workers both print what TLC
  prints, SlushMedium in 17.45 s (10.1x) and MCBoulanger in 16.64 s
  (9.6x), holding 2.1 and 1.3 GB, where one worker holds 1.9 and 1.2.

<!-- results -->

tlaplus/Examples at ca168055339d, every exhaustive-search model (each run killed past 3600 s), and the simulation and generation models with `-seed 1` and `num=` their traceCount, or 100. Measured on arm64 Darwin 25.5.0, one run, wall-clock seconds, one worker.

197 models: 173 same, 10 TLC, 6 manyan, 5 differs, 3 TLC under 4 GB of disk left. Where manyan prints what TLC prints, it is 27.6x as fast (geometric mean).

| model | distinct states | TLC | Manyan | speedup | result |
|---|---:|---:|---:|---:|---|
| Bakery-Boulangerie/MCBakery | 655200 | 6.94 | 1.73 | 4.0x | same |
| Bakery-Boulangerie/MCBoulanger | 7866982 | 159.75 | 50.83 | 3.1x | same |
| CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_1/MC | 0 | 0.43 | 0.00 | 118.2x | same |
| CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_2/MC | 0 | 0.60 | 0.03 | 17.4x | same |
| CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_3/MC |  | 3600.10 |  |  | TLC over 3600.0 s |
| Chameneos/Chameneos | 34534 | 0.82 | 0.05 | 15.3x | same |
| CheckpointCoordination/MCCheckpointCoordination | 901692 | 182.32 | 35.63 | 5.1x | same |
| CheckpointCoordination/MCCheckpointCoordinationFailure | 88152 | 12.39 | 2.29 | 5.4x | same |
| CigaretteSmokers/CigaretteSmokers | 6 | 0.33 | 0.00 | 99.4x | same |
| CoffeeCan/CoffeeCan1000Beans | 501500 | 30.21 | 0.88 | 34.2x | same |
| CoffeeCan/CoffeeCan100Beans | 5150 | 0.80 | 0.01 | 68.7x | same |
| CoffeeCan/CoffeeCan3000Beans | 4504500 | 309.03 |  |  | manyan over 4000 MB |
| DieHard/DieHard | 14 | 0.50 | 0.00 | 136.1x | same |
| DieHard/MCDieHarder | 14 | 0.33 | 0.00 | 106.0x | same |
| DieHard/MCDieHardest | 11566 | 0.61 | 0.03 | 20.2x | same |
| DiningPhilosophers/DiningPhilosophers | 58 | 0.36 | 0.00 | 75.4x | same |
| DiningPhilosophers/DiningPhilosophersPCal | 67 | 0.40 | 0.00 | 98.7x | same |
| DiningPhilosophers/DiningPhilosophers_anim | 58 | 0.40 | 0.01 | 65.1x | same |
| DiningPhilosophers/DiningPhilosophers_stats |  | 0.36 | 0.01 | 28.6x | same |
| Disruptor/MCDisruptor_MPMC | 112929 | 2.59 | 0.49 | 5.3x | same |
| Disruptor/MCDisruptor_MPMC_liveliness | 14365 | 1.67 | 0.20 | 8.3x | same |
| Disruptor/MCDisruptor_SPMC | 8496 | 0.96 | 0.06 | 16.5x | same |
| FiniteMonotonic/MCCRDT | 25000 | 9.10 | 1.00 | 9.1x | same |
| FiniteMonotonic/MCDistributedReplicatedLog | 37 | 0.50 | 0.01 |  | differs |
| FiniteMonotonic/MCReplicatedLog | 1363 | 0.49 | 0.01 | 40.8x | same |
| FlashProtocol/MCFlashWithMutex | 2024 | 0.55 | 0.02 | 23.4x | same |
| FlashProtocol/MCFlashWithMutexLive | 8096 | 8.89 | 0.15 | 59.8x | same |
| GameOfLife/GameOfLife | 65536 | 8.32 | 2.49 | 3.3x | same |
| GermanProtocol/MCGermanCMPWithMutex | 1107 | 0.39 | 0.01 | 66.1x | same |
| GermanProtocol/MCGermanControl | 735 | 0.38 | 0.01 | 59.7x | same |
| GermanProtocol/MCGermanData | 852 | 0.44 | 0.01 | 43.1x | same |
| Huang/Huang | 81256 | 34.59 | 9.23 | 3.7x | same |
| KeyValueStore/MCKVSSafetyLarge |  | 3600.29 |  |  | TLC over 3600.0 s |
| KeyValueStore/MCKVSSafetyMedium | 17220672 | 769.29 | 203.63 | 3.8x | same |
| KeyValueStore/MCKVSSafetySmall | 3409605 | 114.57 | 25.63 | 4.5x | same |
| KeyValueStore/MCKVsnap | 32293 | 7.18 | 1.60 | 4.5x | same |
| KnuthYao/SimKnuthYao |  | 0.38 | 0.12 | 3.3x | same |
| LearnProofs/MCFindHighest | 742 | 0.44 | 0.02 | 22.5x | same |
| LeastCircularSubstring/MCLeastCircularSubstringMedium | 1007232 | 179.43 | 1.38 | 129.6x | same |
| LeastCircularSubstring/MCLeastCircularSubstringSmall | 8554 | 0.60 | 0.02 | 38.1x | same |
| LoopInvariance/MCBinarySearch | 27953 | 1.88 | 0.32 | 5.8x | same |
| LoopInvariance/MCQuicksort | 4548 | 4.50 | 0.50 | 9.1x | same |
| Majority/MCMajority | 2733 | 0.49 | 0.02 | 23.0x | same |
| MisraReachability/MCParReach | 393 | 9.30 | 0.01 | 1298.9x | same |
| MisraReachability/MCReachabilityTestAllGraphs | 0 | 2.27 | 0.82 | 2.8x | same |
| MisraReachability/MCReachabilityTestRandomGraphs | 0 | 0.96 | 0.26 | 3.7x | same |
| MisraReachability/MCReachable | 8 | 57.09 | 0.01 | 10478.7x | same |
| MissionariesAndCannibals/MissionariesAndCannibals | 61 | 0.34 | 0.00 | 85.0x | same |
| Moving_Cat_Puzzle/CatEvenBoxes | 48 | 0.32 | 0.00 | 109.0x | same |
| Moving_Cat_Puzzle/CatOddBoxes | 30 | 0.32 | 0.00 | 117.8x | same |
| MultiCarElevator/ElevatorLivenessLarge | 50653 | 1707.06 | 0.73 | 2346.8x | same |
| MultiCarElevator/ElevatorLivenessMedium | 4122 | 9.28 | 0.06 | 160.0x | same |
| MultiCarElevator/ElevatorSafetyLarge | 59007145 | 1714.54 |  |  | manyan over 4000 MB |
| MultiCarElevator/ElevatorSafetyMedium | 17997111 | 502.32 | 143.53 | 3.5x | same |
| MultiCarElevator/ElevatorSafetySmall | 4122 | 0.75 | 0.02 | 34.0x | same |
| MultiPaxos-SMR/MultiPaxos_MC |  | 3600.05 |  |  | TLC over 3600.0 s |
| MultiPaxos-SMR/MultiPaxos_MC_small | 343796 | 18.22 | 4.74 | 3.8x | same |
| N-Queens/Queens.toolbox/FourQueens/MC | 40 | 0.34 | 0.00 | 88.2x | same |
| N-Queens/QueensPluscal.toolbox/FourQueens/MC | 40 | 0.35 | 0.00 | 99.6x | same |
| NanoBlockchain/MCNanoLarge |  | 3600.16 |  |  | TLC over 3600.0 s |
| NanoBlockchain/MCNanoMedium | 530587 | 14.69 | 4.01 | 3.7x | same |
| NanoBlockchain/MCNanoSmall | 3003 | 0.56 | 0.02 | 24.0x | same |
| Paxos/MCConsensus | 4 | 0.36 | 0.00 | 75.3x | same |
| Paxos/MCPaxos | 25 | 0.49 | 0.01 | 70.3x | same |
| Paxos/MCVoting | 77 | 0.50 | 0.01 | 66.9x | same |
| PaxosHowToWinATuringAward/MCConsensus | 4 | 0.35 | 0.00 | 72.1x | same |
| PaxosHowToWinATuringAward/MCPaxosSmall | 185369 | 97.71 | 15.94 | 6.1x | same |
| PaxosHowToWinATuringAward/MCPaxosTiny | 3921 | 1.71 | 0.20 | 8.8x | same |
| PaxosHowToWinATuringAward/MCVoting | 6752 | 1.86 | 0.19 | 9.6x | same |
| Prisoners/Prisoners | 214 | 0.36 | 0.00 | 88.5x | same |
| Prisoners_Single_Switch/Prisoner | 16 | 0.33 | 0.00 | 104.4x | same |
| Prisoners_Single_Switch/PrisonerLightUnknown | 62 | 0.33 | 0.00 | 101.3x | same |
| Prisoners_Single_Switch/PrisonerSolo | 2 | 0.33 | 0.00 | 105.8x | same |
| Prisoners_Single_Switch/PrisonerSoloLightUnknown | 4 | 0.33 | 0.00 | 108.6x | same |
| ReadersWriters/MC | 21527 | 1.68 | 0.30 | 5.6x | same |
| SDP_Verification/SDP_Attack_New_Solution_Spec/MC | 2881 | 1.22 | 0.06 | 19.9x | same |
| SDP_Verification/SDP_Attack_Spec/MC | 526 | 0.70 | 0.01 | 76.9x | same |
| SimplifiedFastPaxos/FastPaxos | 25617 | 30.29 | 2.66 | 11.4x | same |
| SimplifiedFastPaxos/Paxos | 1207 | 1.16 | 0.11 | 10.7x | same |
| SingleLaneBridge/MC | 3605 | 3.06 | 0.06 | 55.2x | same |
| SlidingPuzzles/SlidingPuzzles | 24005 | 1.29 | 0.28 | 4.6x | same |
| SlidingPuzzles/SlidingPuzzles_anim | 24005 | 1.60 | 0.32 | 5.0x | same |
| SlushProtocol/SlushLarge |  | 3600.16 |  |  | TLC over 3600.0 s |
| SlushProtocol/SlushMedium | 9886336 | 175.85 | 38.20 | 4.6x | same |
| SlushProtocol/SlushSmall | 274678 | 5.59 | 1.02 | 5.5x | same |
| SpanningTree/SpanTree | 1236 | 0.66 | 0.01 | 66.4x | same |
| SpanningTree/SpanTreeRandom | 65396 | 14.47 | 0.57 |  | differs |
| SpanningTree/SpanTreeTest4Nodes | 3984 | 0.76 | 0.03 | 28.5x | same |
| SpanningTree/SpanTreeTest5Nodes | 410112 | 547.10 | 172.46 | 3.2x | same |
| SpecificationRefinement/abstract | 4 | 0.32 | 0.00 | 93.7x | same |
| SpecificationRefinement/bad | 12 | 0.32 | 0.00 | 85.7x | same |
| SpecificationRefinement/good | 9 | 0.33 | 0.00 | 96.5x | same |
| SpecifyingSystems/AdvancedExamples/MCInnerSequential | 3528 | 1.02 | 0.04 | 27.4x | same |
| SpecifyingSystems/AdvancedExamples/MCInnerSerial | 195 | 369.52 | 202.17 | 1.8x | same |
| SpecifyingSystems/AsynchronousInterface/AsynchInterface | 12 | 0.31 | 0.00 | 106.7x | same |
| SpecifyingSystems/AsynchronousInterface/Channel | 12 | 0.32 | 0.00 | 118.1x | same |
| SpecifyingSystems/AsynchronousInterface/PrintValues | 0 | 0.33 | 0.00 | 109.8x | same |
| SpecifyingSystems/CachingMemory/MCInternalMemory | 4408 | 0.39 | 0.01 | 49.4x | same |
| SpecifyingSystems/CachingMemory/MCWriteThroughCache | 5196 | 0.63 | 0.06 | 11.3x | same |
| SpecifyingSystems/FIFO/MCInnerFIFO | 3864 | 0.37 | 0.01 | 61.6x | same |
| SpecifyingSystems/HourClock/HourClock | 12 | 0.32 | 0.00 | 118.2x | same |
| SpecifyingSystems/HourClock/HourClock2 | 12 | 0.33 | 0.00 | 124.6x | same |
| SpecifyingSystems/Liveness/LiveHourClock | 12 | 0.32 | 0.00 | 118.1x | same |
| SpecifyingSystems/Liveness/MCLiveInternalMemory | 4408 | 0.87 | 0.04 | 21.7x | same |
| SpecifyingSystems/Liveness/MCLiveWriteThroughCache | 5196 | 1.34 | 0.22 | 6.0x | same |
| SpecifyingSystems/RealTime/MCRealTimeHourClock | 216 | 0.35 | 0.00 | 102.5x | same |
| SpecifyingSystems/SimpleMath/SimpleMath | 0 | 0.32 | 0.00 | 112.3x | same |
| SpecifyingSystems/TLC/ABCorrectness | 20 | 0.32 | 0.00 | 111.2x | same |
| SpecifyingSystems/TLC/MCAlternatingBit | 240 | 0.43 | 0.01 | 86.3x | same |
| StaleViewShrink/StaleShrink | 16848 | 0.64 | 0.04 | 18.2x | same |
| StaleViewShrink/StaleShrinkV6Wait2x | 43348 | 0.88 | 0.08 | 10.6x | same |
| StaleViewShrink/StaleShrinkV3Cascade | 32551 | 0.74 | 0.06 | 12.6x | same |
| StaleViewShrink/StaleShrinkV6TooShort | 2132 | 0.44 | 0.01 | 66.1x | same |
| Stones/Stones | 0 | 0.40 | 0.01 | 46.5x | same |
| TLC/TestGraphs | 2590 | 0.93 | 0.04 | 21.0x | same |
| TLC/TestMCReachability | 17938831 | 1237.36 |  |  | manyan over 4000 MB |
| TeachingConcurrency/Simple | 723 | 0.36 | 0.01 | 70.7x | same |
| TeachingConcurrency/SimpleRegular | 277726 | 3.50 | 0.71 | 4.9x | same |
| TransitiveClosure/TransitiveClosure | 0 | 0.66 | 0.10 | 6.9x | same |
| TwoPhase/MCTwoPhase | 4 | 0.33 | 0.00 | 98.8x | same |
| YoYo/MCYoYoNoPruning | 60 | 0.49 | 0.01 | 73.7x | same |
| YoYo/MCYoYoPruning | 102 | 0.54 | 0.01 | 66.5x | same |
| YoYo/YoYoAllGraphs | 26731 | 3.97 | 0.56 | 7.1x | same |
| aba-asyn-byz/aba_asyn_byz | 5843977 | 1085.50 |  |  | manyan over 4000 MB |
| acp/ACP_NB_TLC | 4284 | 1.09 | 0.03 | 39.7x | same |
| acp/ACP_NB_WRONG_TLC | 11852 | 0.61 | 0.03 | 21.9x | same |
| acp/ACP_SB_TLC | 54944 | 0.97 | 0.09 | 11.1x | same |
| allocator/AllocatorImplementation | 17701 | 5.50 | 0.72 | 7.6x | same |
| allocator/AllocatorRefinement | 1690 | 0.75 | 0.04 | 18.0x | same |
| allocator/SchedulingAllocator | 1690 | 1.74 | 0.02 | 72.2x | same |
| allocator/SimpleAllocator | 400 | 0.87 | 0.02 | 42.4x | same |
| barriers/Barrier | 64 | 0.32 | 0.00 | 102.2x | same |
| barriers/Barriers | 29279 | 2.46 | 0.37 | 6.6x | same |
| bcastByz/bcastByz | 14424 | 9.86 | 0.31 | 31.9x | same |
| bcastByz/bcastByzNoBcast | 45 | 0.61 | 0.01 | 68.8x | same |
| bcastFolklore/bcastFolklore |  | 1371.24 |  |  | TLC under 4 GB of disk left |
| bosco/bosco | 1072452 | 555.57 | 155.74 | 3.6x | same |
| braf/BufferedRandomAccessFile | 3316 | 36.29 | 8.58 | 4.2x | same |
| btree/MCbtree | 374727 | 28.52 | 4.27 | 6.7x | same |
| btree/kvstore | 2641 | 0.43 | 0.01 | 48.3x | same |
| byihive/VoucherCancel | 4199 | 0.54 | 0.06 | 9.6x | same |
| byihive/VoucherIssue | 4199 | 0.66 | 0.07 | 8.8x | same |
| byihive/VoucherLifeCycle | 64 | 0.32 | 0.00 | 106.3x | same |
| byihive/VoucherRedeem | 4199 | 0.54 | 0.05 | 9.9x | same |
| byihive/VoucherTransfer | 4197 | 0.54 | 0.06 | 9.7x | same |
| byzpaxos/BPConProof |  | 2521.85 |  |  | TLC under 4 GB of disk left |
| byzpaxos/Consensus | 4 | 0.38 | 0.01 | 60.7x | same |
| byzpaxos/PConProof | 1009133 | 1221.57 | 186.94 | 6.5x | same |
| byzpaxos/VoteProof | 6962 | 8.18 | 1.11 | 7.4x | same |
| c1cs/c1cs |  | 3600.19 |  |  | TLC over 3600.0 s |
| cf1s-folklore/cf1s_folklore | 2057174 | 154.09 | 7.88 | 19.6x | same |
| chang_roberts/MCChangRoberts | 137 | 0.36 | 0.00 | 89.4x | same |
| dag-consensus/BlockDagTest | 0 | 0.32 | 0.00 | 83.3x | same |
| dag-consensus/TLCSailfish1 | 109604 | 34.46 | 9.16 | 3.8x | same |
| dag-consensus/TLCSailfish2 |  | 3600.12 |  |  | TLC over 3600.0 s |
| detector_chan96/EnvironmentController |  | 3600.08 |  |  | TLC over 3600.0 s |
| dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC | 90882 | 16.92 | 0.56 | 30.2x | same |
| dijkstra-mutex/DijkstraMutex.toolbox/Safety-4-processors/MC | 33288512 | 271.96 |  |  | manyan over 4000 MB |
| diskpaxos/MC_HDiskSynod |  | 3600.09 |  |  | TLC over 3600.0 s |
| echo/MCEcho | 75 | 0.55 | 0.01 | 61.0x | same |
| ewd426/SimTokenRing |  | 3.12 | 0.93 | 3.4x | same |
| ewd426/TokenRing | 46656 | 1.40 | 0.09 | 15.1x | same |
| ewd687a/EWD687a_anim |  | 1.02 | 0.01 |  | differs |
| ewd687a/MCEWD687a | 18028 | 3.44 | 0.29 | 11.9x | same |
| ewd840/EWD840 | 302 | 0.50 | 0.01 | 83.9x | same |
| ewd840/EWD840_anim |  | 0.76 | 0.06 | 13.1x | same |
| ewd840/EWD840_json | 1566 | 0.43 | 0.01 | 61.8x | same |
| ewd840/SyncTerminationDetection | 129 | 0.35 | 0.00 | 88.6x | same |
| ewd998/AsyncTerminationDetection | 4097 | 0.60 | 0.02 | 28.8x | same |
| ewd998/EWD998 |  | 1192.82 |  |  | manyan over 4000 MB |
| ewd998/EWD998Small | 1520618 | 22.62 | 7.14 | 3.2x | same |
| ewd998/EWD998Chan | 1524022 | 674.80 | 103.36 | 6.5x | same |
| ewd998/EWD998ChanID | 14 | 0.66 | 0.02 | 32.6x | same |
| ewd998/EWD998ChanID_export |  | 3600.14 |  |  | TLC over 3600.0 s |
| ewd998/EWD998ChanID_shiviz |  | 1489.33 |  |  | TLC under 4 GB of disk left |
| ewd998/EWD998ChanTrace |  | 0.44 | 0.01 | 54.2x | same |
| ewd998/EWD998PCal | 321370 | 27.04 | 6.68 | 4.0x | same |
| ewd998/SmokeEWD998 |  | 0.87 | 0.07 | 12.5x | same |
| ewd998/SmokeEWD998_SC | 0 | 2.04 | 0.01 |  | differs |
| glowingRaccoon/clean | 63 | 0.33 | 0.00 | 103.2x | same |
| glowingRaccoon/product | 305 | 0.43 | 0.01 | 52.1x | same |
| glowingRaccoon/stages | 83 | 0.35 | 0.00 | 101.5x | same |
| lamport_mutex/MCLamportMutex | 724274 | 10.57 | 2.97 | 3.6x | same |
| locks_auxiliary_vars/Lock | 12 | 0.33 | 0.00 | 95.2x | same |
| locks_auxiliary_vars/LockHS | 28 | 0.44 | 0.01 | 74.4x | same |
| locks_auxiliary_vars/Peterson | 42 | 0.35 | 0.00 | 89.0x | same |
| nbacc_ray97/nbacc_ray97 | 3016 | 0.54 | 0.02 | 33.8x | same |
| nbacg_guer01/nbacg_guer01 | 24922 | 2.39 | 0.09 | 27.3x | same |
| spanning/MC_spanning | 5 | 0.33 | 0.00 | 105.1x | same |
| sums_even/MC_sums_even | 0 | 0.50 | 0.04 | 11.8x | same |
| tcp/MCtcp | 1182 | 0.61 | 0.02 | 38.4x | same |
| tower_of_hanoi/Hanoi.toolbox/Model_1/MC | 233 | 0.36 | 0.01 |  | differs |
| tower_of_hanoi/Hanoi_anim | 25 | 0.49 | 0.01 | 64.9x | same |
| transaction_commit/2PCwithBTM | 1245 | 0.37 | 0.01 | 62.8x | same |
| transaction_commit/PaxosCommit | 1321761 | 122.44 | 19.15 | 6.4x | same |
| transaction_commit/TCommit | 34 | 0.33 | 0.00 | 99.8x | same |
| transaction_commit/TwoPhase | 288 | 0.32 | 0.00 | 90.1x | same |
