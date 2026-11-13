# Full benchmark

`make full-bench` checks the models of
[tlaplus/Examples](https://github.com/tlaplus/Examples) with Manyan and with
TLC, and writes this report. `make bench` ([benchmark](benchmark.md)) is the
quick one for day-to-day work; this one takes hours and asks a stronger
question: does Manyan print what TLC prints on specs it was not written for?

Examples, CommunityModules and TLAPS are pinned in the Makefile. Each model
runs once with one worker, killed past 15 minutes or 4 GB. TLC's results are
cached under `.obj` and the diffs of the models that differ are written to
`.obj/fullbench.diff`. `ONLY=DieHard` runs the models whose path contains
DieHard; `MAX_RUNTIME=00:00:30` keeps those recorded to run in 30 seconds.

Of Examples' 243 models, it checks the 174 that TLC searches exhaustively
in a recorded 10 minutes or less, and the 6 that simulate or generate
behaviors, fixed by `-seed 1` and `num=`; the rest are Apalache's
(symbolic, 46), or longer or not timed (17). Where TLC is killed, there is
nothing to compare. Four differ, for reasons Manyan keeps:

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

## Gaps

What the full bench does not yet compare, and what would close each gap.
A model leaves this list when it gets a row in the results.

| gap | models | to close |
|---|---:|---|
| runtime not recorded | 10 | Run once by hand (below): eight need more than 15 minutes of TLC, a longer cap as below |
| TLC over 15 minutes | 4 | A longer cap for TLC, run once; its results stay cached |
| recorded over 10 minutes | 7 | A run with a larger `MAX_RUNTIME`, hours long |
| more than one worker | 7 | Run those recorded over a minute with `-workers 4` too |
| symbolic | 46 | None: these are Apalache's models, not TLC's |

- More than one worker: the 167 models recorded to run in a minute or
  less were run once with `-workers 4` (by an engine wrapping
  `manyan -workers 4`): 160 print what TLC prints, as with one worker,
  and the four that differ with one worker differ alike; the run found
  TLCSailfish1's parse failure, since fixed. SlushMedium and
  MCBoulanger went past the 4 GB guard, which sums the resident memory
  of the worker processes, pages they share counted in each: on
  SlushSmall, 242 MB summed with four workers where the search process
  holds 67 MB, as it does alone (65 MB). With one worker both run in
  less than 2 GB.
- Runtime not recorded: CarTalkPuzzle Model_3, SpanTreeTest5Nodes,
  TestMCReachability, BPConProof, c1cs, TLCSailfish2, MC_HDiskSynod,
  EWD998ChanID_export, EWD998ChanID_shiviz, SmokeEWD998_SC. Run once by
  hand: SpanTreeTest5Nodes prints what TLC prints (TLC 590 s, Manyan
  168 s); SmokeEWD998_SC runs TLC itself through IOExec; the other eight
  run past 15 minutes for TLC (CarTalkPuzzle Model_3 filters 121^5
  functions), and past 5 for Manyan.
- TLC over 15 minutes: ElevatorSafetyLarge (Manyan 774 s), aba_asyn_byz
  (Manyan 31 s), PConProof (Manyan 185 s), MultiPaxos_MC (Manyan over 15 minutes as
  well).
- Recorded over 10 minutes: MCKVSSafetyLarge (7 h 16 min),
  EnvironmentController (2 h), SlushLarge and EWD998 (50 min each),
  bcastFolklore (30 min), MCNanoLarge (20 min), ElevatorLivenessLarge
  (11 min).

<!-- results -->

tlaplus/Examples at ca168055339d, the exhaustive-search models recorded to run in at most 00:10:00, and the simulation and generation models with `-seed 1` and `num=` their traceCount, or 100. Measured on arm64 Darwin 25.5.0, one run, wall-clock seconds, one worker.

180 models: 172 same, 4 differs, 4 TLC. Where manyan prints what TLC prints, it is 21.3x as fast (geometric mean).

| model | distinct states | TLC | Manyan | speedup | result |
|---|---:|---:|---:|---:|---|
| Bakery-Boulangerie/MCBakery | 655200 | 6.94 | 1.81 | 3.8x | same |
| Bakery-Boulangerie/MCBoulanger | 7866982 | 159.75 | 51.29 | 3.1x | same |
| CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_1/MC | 0 | 0.43 | 0.01 | 72.5x | same |
| CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_2/MC | 0 | 0.60 | 0.04 | 16.2x | same |
| Chameneos/Chameneos | 34534 | 0.82 | 0.06 | 13.2x | same |
| CheckpointCoordination/MCCheckpointCoordination | 901692 | 182.32 | 35.90 | 5.1x | same |
| CheckpointCoordination/MCCheckpointCoordinationFailure | 88152 | 12.39 | 2.19 | 5.7x | same |
| CigaretteSmokers/CigaretteSmokers | 6 | 0.33 | 0.01 | 57.8x | same |
| CoffeeCan/CoffeeCan1000Beans | 501500 | 30.21 | 0.90 | 33.7x | same |
| CoffeeCan/CoffeeCan100Beans | 5150 | 0.80 | 0.01 | 67.1x | same |
| CoffeeCan/CoffeeCan3000Beans | 4504500 | 309.03 | 12.10 | 25.5x | same |
| DieHard/DieHard | 14 | 0.50 | 0.01 | 85.6x | same |
| DieHard/MCDieHarder | 14 | 0.33 | 0.01 | 59.9x | same |
| DieHard/MCDieHardest | 11566 | 0.61 | 0.04 | 16.6x | same |
| DiningPhilosophers/DiningPhilosophers | 58 | 0.36 | 0.01 | 64.4x | same |
| DiningPhilosophers/DiningPhilosophersPCal | 67 | 0.40 | 0.01 | 72.1x | same |
| DiningPhilosophers/DiningPhilosophers_anim | 58 | 0.40 | 0.01 | 33.4x | same |
| DiningPhilosophers/DiningPhilosophers_stats |  | 0.36 | 0.01 | 25.4x | same |
| Disruptor/MCDisruptor_MPMC | 112929 | 2.59 | 0.55 | 4.7x | same |
| Disruptor/MCDisruptor_MPMC_liveliness | 14365 | 1.67 | 0.20 | 8.2x | same |
| Disruptor/MCDisruptor_SPMC | 8496 | 0.96 | 0.05 | 19.4x | same |
| FiniteMonotonic/MCCRDT | 25000 | 9.10 | 1.08 | 8.4x | same |
| FiniteMonotonic/MCDistributedReplicatedLog | 37 | 0.50 | 0.01 |  | differs |
| FiniteMonotonic/MCReplicatedLog | 1363 | 0.49 | 0.01 | 34.1x | same |
| FlashProtocol/MCFlashWithMutex | 2024 | 0.55 | 0.02 | 22.7x | same |
| FlashProtocol/MCFlashWithMutexLive | 8096 | 8.89 | 0.17 | 51.7x | same |
| GameOfLife/GameOfLife | 65536 | 8.32 | 2.56 | 3.2x | same |
| GermanProtocol/MCGermanCMPWithMutex | 1107 | 0.39 | 0.01 | 33.2x | same |
| GermanProtocol/MCGermanControl | 735 | 0.38 | 0.01 | 33.0x | same |
| GermanProtocol/MCGermanData | 852 | 0.44 | 0.01 | 37.6x | same |
| Huang/Huang | 81256 | 34.59 | 38.71 | 0.9x | same |
| KeyValueStore/MCKVSSafetyMedium | 17220672 | 769.29 | 206.90 | 3.7x | same |
| KeyValueStore/MCKVSSafetySmall | 3409605 | 114.57 | 25.53 | 4.5x | same |
| KeyValueStore/MCKVsnap | 32293 | 7.18 | 1.60 | 4.5x | same |
| KnuthYao/SimKnuthYao |  | 0.38 | 0.18 | 2.1x | same |
| LearnProofs/MCFindHighest | 742 | 0.44 | 0.03 | 17.4x | same |
| LeastCircularSubstring/MCLeastCircularSubstringMedium | 1007232 | 179.43 | 1.40 | 128.6x | same |
| LeastCircularSubstring/MCLeastCircularSubstringSmall | 8554 | 0.60 | 0.01 | 42.3x | same |
| LoopInvariance/MCBinarySearch | 27953 | 1.88 | 0.39 | 4.8x | same |
| LoopInvariance/MCQuicksort | 4548 | 4.50 | 0.56 | 8.1x | same |
| Majority/MCMajority | 2733 | 0.49 | 0.02 | 20.0x | same |
| MisraReachability/MCParReach | 393 | 9.30 | 0.01 | 808.1x | same |
| MisraReachability/MCReachabilityTestAllGraphs | 0 | 2.27 | 0.92 | 2.5x | same |
| MisraReachability/MCReachabilityTestRandomGraphs | 0 | 0.96 | 0.32 | 3.0x | same |
| MisraReachability/MCReachable | 8 | 57.09 | 0.01 | 5100.2x | same |
| MissionariesAndCannibals/MissionariesAndCannibals | 61 | 0.34 | 0.01 | 60.9x | same |
| Moving_Cat_Puzzle/CatEvenBoxes | 48 | 0.32 | 0.01 | 56.7x | same |
| Moving_Cat_Puzzle/CatOddBoxes | 30 | 0.32 | 0.01 | 57.9x | same |
| MultiCarElevator/ElevatorLivenessMedium | 4122 | 9.28 | 0.06 | 152.7x | same |
| MultiCarElevator/ElevatorSafetyLarge |  | 900.06 | 686.97 |  | TLC over 900 s |
| MultiCarElevator/ElevatorSafetyMedium | 17997111 | 502.32 | 147.29 | 3.4x | same |
| MultiCarElevator/ElevatorSafetySmall | 4122 | 0.75 | 0.03 | 29.6x | same |
| MultiPaxos-SMR/MultiPaxos_MC |  | 900.02 |  |  | TLC over 900 s |
| MultiPaxos-SMR/MultiPaxos_MC_small | 343796 | 18.22 | 4.80 | 3.8x | same |
| N-Queens/Queens.toolbox/FourQueens/MC | 40 | 0.34 | 0.00 | 70.2x | same |
| N-Queens/QueensPluscal.toolbox/FourQueens/MC | 40 | 0.35 | 0.01 | 62.8x | same |
| NanoBlockchain/MCNanoMedium | 530587 | 14.69 | 4.16 | 3.5x | same |
| NanoBlockchain/MCNanoSmall | 3003 | 0.56 | 0.04 | 15.1x | same |
| Paxos/MCConsensus | 4 | 0.36 | 0.01 | 64.2x | same |
| Paxos/MCPaxos | 25 | 0.49 | 0.01 | 42.7x | same |
| Paxos/MCVoting | 77 | 0.50 | 0.01 | 43.1x | same |
| PaxosHowToWinATuringAward/MCConsensus | 4 | 0.35 | 0.01 | 62.9x | same |
| PaxosHowToWinATuringAward/MCPaxosSmall | 185369 | 97.71 | 16.25 | 6.0x | same |
| PaxosHowToWinATuringAward/MCPaxosTiny | 3921 | 1.71 | 0.20 | 8.5x | same |
| PaxosHowToWinATuringAward/MCVoting | 6752 | 1.86 | 0.20 | 9.4x | same |
| Prisoners/Prisoners | 214 | 0.36 | 0.01 | 65.2x | same |
| Prisoners_Single_Switch/Prisoner | 16 | 0.33 | 0.01 | 58.9x | same |
| Prisoners_Single_Switch/PrisonerLightUnknown | 62 | 0.33 | 0.01 | 58.7x | same |
| Prisoners_Single_Switch/PrisonerSolo | 2 | 0.33 | 0.01 | 58.6x | same |
| Prisoners_Single_Switch/PrisonerSoloLightUnknown | 4 | 0.33 | 0.01 | 59.2x | same |
| ReadersWriters/MC | 21527 | 1.68 | 0.33 | 5.1x | same |
| SDP_Verification/SDP_Attack_New_Solution_Spec/MC | 2881 | 1.22 | 0.09 | 14.3x | same |
| SDP_Verification/SDP_Attack_Spec/MC | 526 | 0.70 | 0.01 | 59.6x | same |
| SimplifiedFastPaxos/FastPaxos | 25617 | 30.29 | 2.75 | 11.0x | same |
| SimplifiedFastPaxos/Paxos | 1207 | 1.16 | 0.13 | 8.8x | same |
| SingleLaneBridge/MC | 3605 | 3.06 | 0.06 | 49.6x | same |
| SlidingPuzzles/SlidingPuzzles | 24005 | 1.29 | 0.32 | 4.0x | same |
| SlidingPuzzles/SlidingPuzzles_anim | 24005 | 1.60 | 0.34 | 4.7x | same |
| SlushProtocol/SlushMedium | 9886336 | 175.85 | 38.13 | 4.6x | same |
| SlushProtocol/SlushSmall | 274678 | 5.59 | 1.08 | 5.2x | same |
| SpanningTree/SpanTree | 1236 | 0.66 | 0.01 | 55.3x | same |
| SpanningTree/SpanTreeRandom | 65396 | 14.47 | 0.61 |  | differs |
| SpanningTree/SpanTreeTest4Nodes | 3984 | 0.76 | 0.04 | 20.3x | same |
| SpecificationRefinement/abstract | 4 | 0.32 | 0.01 | 56.9x | same |
| SpecificationRefinement/bad | 12 | 0.32 | 0.01 | 54.8x | same |
| SpecificationRefinement/good | 9 | 0.33 | 0.01 | 58.4x | same |
| SpecifyingSystems/AdvancedExamples/MCInnerSequential | 3528 | 1.02 | 0.04 | 27.6x | same |
| SpecifyingSystems/AdvancedExamples/MCInnerSerial | 195 | 369.52 | 222.21 | 1.7x | same |
| SpecifyingSystems/AsynchronousInterface/AsynchInterface | 12 | 0.31 | 0.01 | 56.2x | same |
| SpecifyingSystems/AsynchronousInterface/Channel | 12 | 0.32 | 0.01 | 58.2x | same |
| SpecifyingSystems/AsynchronousInterface/PrintValues | 0 | 0.33 | 0.01 | 60.2x | same |
| SpecifyingSystems/CachingMemory/MCInternalMemory | 4408 | 0.39 | 0.01 | 34.0x | same |
| SpecifyingSystems/CachingMemory/MCWriteThroughCache | 5196 | 0.63 | 0.06 | 10.1x | same |
| SpecifyingSystems/FIFO/MCInnerFIFO | 3864 | 0.37 | 0.01 | 32.0x | same |
| SpecifyingSystems/HourClock/HourClock | 12 | 0.32 | 0.01 | 56.6x | same |
| SpecifyingSystems/HourClock/HourClock2 | 12 | 0.33 | 0.01 | 58.4x | same |
| SpecifyingSystems/Liveness/LiveHourClock | 12 | 0.32 | 0.01 | 58.5x | same |
| SpecifyingSystems/Liveness/MCLiveInternalMemory | 4408 | 0.87 | 0.04 | 22.2x | same |
| SpecifyingSystems/Liveness/MCLiveWriteThroughCache | 5196 | 1.34 | 0.22 | 6.0x | same |
| SpecifyingSystems/RealTime/MCRealTimeHourClock | 216 | 0.35 | 0.01 | 63.1x | same |
| SpecifyingSystems/SimpleMath/SimpleMath | 0 | 0.32 | 0.01 | 55.4x | same |
| SpecifyingSystems/TLC/ABCorrectness | 20 | 0.32 | 0.01 | 57.3x | same |
| SpecifyingSystems/TLC/MCAlternatingBit | 240 | 0.43 | 0.01 | 77.2x | same |
| StaleViewShrink/StaleShrink | 16848 | 0.64 | 0.04 | 16.3x | same |
| StaleViewShrink/StaleShrinkV6Wait2x | 43348 | 0.88 | 0.09 | 10.1x | same |
| StaleViewShrink/StaleShrinkV3Cascade | 32551 | 0.74 | 0.06 | 12.1x | same |
| StaleViewShrink/StaleShrinkV6TooShort | 2132 | 0.44 | 0.01 | 37.7x | same |
| Stones/Stones | 0 | 0.40 | 0.01 | 34.6x | same |
| TLC/TestGraphs | 2590 | 0.93 | 0.04 | 22.8x | same |
| TeachingConcurrency/Simple | 723 | 0.36 | 0.01 | 65.1x | same |
| TeachingConcurrency/SimpleRegular | 277726 | 3.50 | 0.75 | 4.6x | same |
| TransitiveClosure/TransitiveClosure | 0 | 0.66 | 0.11 | 5.9x | same |
| TwoPhase/MCTwoPhase | 4 | 0.33 | 0.01 | 59.7x | same |
| YoYo/MCYoYoNoPruning | 60 | 0.49 | 0.01 | 42.0x | same |
| YoYo/MCYoYoPruning | 102 | 0.54 | 0.01 | 46.6x | same |
| YoYo/YoYoAllGraphs | 26731 | 3.97 | 0.55 | 7.2x | same |
| aba-asyn-byz/aba_asyn_byz |  | 900.13 | 36.42 |  | TLC over 900 s |
| acp/ACP_NB_TLC | 4284 | 1.09 | 0.03 | 43.0x | same |
| acp/ACP_NB_WRONG_TLC | 11852 | 0.61 | 0.04 | 16.6x | same |
| acp/ACP_SB_TLC | 54944 | 0.97 | 0.09 | 11.0x | same |
| allocator/AllocatorImplementation | 17701 | 5.50 | 0.76 | 7.3x | same |
| allocator/AllocatorRefinement | 1690 | 0.75 | 0.04 | 16.9x | same |
| allocator/SchedulingAllocator | 1690 | 1.74 | 0.02 | 71.0x | same |
| allocator/SimpleAllocator | 400 | 0.87 | 0.02 | 34.9x | same |
| barriers/Barrier | 64 | 0.32 | 0.01 | 58.0x | same |
| barriers/Barriers | 29279 | 2.46 | 0.44 | 5.6x | same |
| bcastByz/bcastByz | 14424 | 9.86 | 0.33 | 30.2x | same |
| bcastByz/bcastByzNoBcast | 45 | 0.61 | 0.01 | 51.9x | same |
| bosco/bosco | 1072452 | 555.57 | 156.48 | 3.6x | same |
| braf/BufferedRandomAccessFile | 3316 | 36.29 | 9.13 | 4.0x | same |
| btree/MCbtree | 374727 | 28.52 | 4.37 | 6.5x | same |
| btree/kvstore | 2641 | 0.43 | 0.01 | 36.5x | same |
| byihive/VoucherCancel | 4199 | 0.54 | 0.06 | 8.7x | same |
| byihive/VoucherIssue | 4199 | 0.66 | 0.09 | 7.7x | same |
| byihive/VoucherLifeCycle | 64 | 0.32 | 0.01 | 57.8x | same |
| byihive/VoucherRedeem | 4199 | 0.54 | 0.06 | 8.8x | same |
| byihive/VoucherTransfer | 4197 | 0.54 | 0.06 | 8.8x | same |
| byzpaxos/Consensus | 4 | 0.38 | 0.01 | 65.5x | same |
| byzpaxos/PConProof |  | 900.14 | 189.42 |  | TLC over 900 s |
| byzpaxos/VoteProof | 6962 | 8.18 | 1.13 | 7.2x | same |
| cf1s-folklore/cf1s_folklore | 2057174 | 154.09 | 7.43 | 20.7x | same |
| chang_roberts/MCChangRoberts | 137 | 0.36 | 0.01 | 64.2x | same |
| dag-consensus/BlockDagTest | 0 | 0.32 | 0.01 | 57.7x | same |
| dag-consensus/TLCSailfish1 | 109604 | 34.46 | 9.60 | 3.6x | same |
| dijkstra-mutex/DijkstraMutex.toolbox/LSpec-model/MC | 90882 | 16.92 | 0.49 | 34.4x | same |
| dijkstra-mutex/DijkstraMutex.toolbox/Safety-4-processors/MC | 33288512 | 271.96 | 92.93 | 2.9x | same |
| echo/MCEcho | 75 | 0.55 | 0.01 | 92.6x | same |
| ewd426/SimTokenRing |  | 3.12 | 0.96 | 3.3x | same |
| ewd426/TokenRing | 46656 | 1.40 | 0.09 | 15.5x | same |
| ewd687a/EWD687a_anim |  | 1.02 | 0.01 |  | differs |
| ewd687a/MCEWD687a | 18028 | 3.44 | 0.32 | 10.6x | same |
| ewd840/EWD840 | 302 | 0.50 | 0.01 | 84.5x | same |
| ewd840/EWD840_anim |  | 0.76 | 0.06 | 12.1x | same |
| ewd840/EWD840_json | 1566 | 0.43 | 0.01 | 36.4x | same |
| ewd840/SyncTerminationDetection | 129 | 0.35 | 0.01 | 60.2x | same |
| ewd998/AsyncTerminationDetection | 4097 | 0.60 | 0.02 | 24.4x | same |
| ewd998/EWD998Small | 1520618 | 22.62 | 10.66 | 2.1x | same |
| ewd998/EWD998Chan | 1524022 | 674.80 | 102.87 | 6.6x | same |
| ewd998/EWD998ChanID | 14 | 0.66 | 0.03 | 26.2x | same |
| ewd998/EWD998ChanTrace |  | 0.44 | 0.01 | 37.4x | same |
| ewd998/EWD998PCal | 321370 | 27.04 | 7.18 | 3.8x | same |
| ewd998/SmokeEWD998 |  | 0.87 | 0.17 | 5.1x | same |
| glowingRaccoon/clean | 63 | 0.33 | 0.01 | 55.3x | same |
| glowingRaccoon/product | 305 | 0.43 | 0.01 | 37.5x | same |
| glowingRaccoon/stages | 83 | 0.35 | 0.01 | 62.5x | same |
| lamport_mutex/MCLamportMutex | 724274 | 10.57 | 3.12 | 3.4x | same |
| locks_auxiliary_vars/Lock | 12 | 0.33 | 0.01 | 58.5x | same |
| locks_auxiliary_vars/LockHS | 28 | 0.44 | 0.01 | 37.8x | same |
| locks_auxiliary_vars/Peterson | 42 | 0.35 | 0.01 | 64.0x | same |
| nbacc_ray97/nbacc_ray97 | 3016 | 0.54 | 0.01 | 37.3x | same |
| nbacg_guer01/nbacg_guer01 | 24922 | 2.39 | 0.09 | 27.8x | same |
| spanning/MC_spanning | 5 | 0.33 | 0.01 | 58.0x | same |
| sums_even/MC_sums_even | 0 | 0.50 | 0.05 | 10.0x | same |
| tcp/MCtcp | 1182 | 0.61 | 0.02 | 38.4x | same |
| tower_of_hanoi/Hanoi.toolbox/Model_1/MC | 233 | 0.36 | 0.01 |  | differs |
| tower_of_hanoi/Hanoi_anim | 25 | 0.49 | 0.01 | 42.6x | same |
| transaction_commit/2PCwithBTM | 1245 | 0.37 | 0.01 | 65.7x | same |
| transaction_commit/PaxosCommit | 1321761 | 122.44 | 19.66 | 6.2x | same |
| transaction_commit/TCommit | 34 | 0.33 | 0.01 | 57.9x | same |
| transaction_commit/TwoPhase | 288 | 0.32 | 0.01 | 57.3x | same |
