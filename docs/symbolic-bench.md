# Symbolic benchmark

<!-- results -->

tlaplus/Examples at ca168055339d, the models its manifests check with Apalache, to length 5. Measured on arm64 Darwin 25.5.0, one run, wall-clock seconds.

46 models: 46 same. Where manyan gives Apalache's outcome, it is 266.9x as fast (geometric mean).

| model | outcome | Apalache | Manyan | speedup | result |
|---|---|---:|---:|---:|---|
| CigaretteSmokers/APCigaretteSmokers | NoError | 2.59 | 0.01 | 439.9x | same |
| CoffeeCan/APCoffeeCan | NoError | 1.76 | 0.03 | 70.3x | same |
| DieHard/APDieHarder | NoError | 3.50 | 0.04 | 95.0x | same |
| DiningPhilosophers/APDiningPhilosophersPCal | NoError | 6.53 | 0.01 | 1149.4x | same |
| Disruptor/APDisruptor_MPMC | NoError | 3.62 | 0.01 | 310.3x | same |
| Disruptor/APDisruptor_SPMC | NoError | 2.38 | 0.01 | 407.3x | same |
| EinsteinRiddle/Einstein | Error FindSolution 1 | 2.39 | 0.01 | 205.2x | same |
| FiniteMonotonic/APCRDT | NoError | 11.03 | 0.01 | 951.2x | same |
| FiniteMonotonic/APReplicatedLog | NoError | 1.89 | 0.01 | 327.4x | same |
| FlashProtocol/APFlashWithMutex | NoError | 36.73 | 0.36 | 102.0x | same |
| GermanProtocol/APGermanCMPWithMutex | NoError | 5.31 | 0.01 | 455.7x | same |
| GermanProtocol/APGermanControl | NoError | 2.15 | 0.01 | 183.2x | same |
| GermanProtocol/APGermanData | NoError | 2.95 | 0.01 | 208.1x | same |
| MisraReachability/APParReach | NoError | 2.38 | 0.01 | 207.5x | same |
| MissionariesAndCannibals/APMissionariesAndCannibals | NoError | 1.96 | 0.01 | 344.1x | same |
| Moving_Cat_Puzzle/APCat | NoError | 1.60 | 0.01 | 290.2x | same |
| ReadersWriters/APReadersWriters | NoError | 2.07 | 0.01 | 369.1x | same |
| SpanningTree/APSpanTree | ExecutionsTooShort | 1.75 | 0.01 | 150.4x | same |
| SpecifyingSystems/AsynchronousInterface/APAsynchInterface | NoError | 1.45 | 0.01 | 256.4x | same |
| SpecifyingSystems/AsynchronousInterface/APChannel | NoError | 1.55 | 0.01 | 275.8x | same |
| SpecifyingSystems/Composing/APChannel | NoError | 1.55 | 0.01 | 272.4x | same |
| SpecifyingSystems/Composing/APHourClock | NoError | 1.35 | 0.01 | 240.7x | same |
| SpecifyingSystems/FIFO/APChannel | NoError | 1.55 | 0.01 | 273.4x | same |
| SpecifyingSystems/FIFO/APInnerFIFO | NoError | 1.76 | 0.01 | 296.0x | same |
| SpecifyingSystems/FIFO/APInnerFIFOInstanced | NoError | 1.71 | 0.01 | 307.8x | same |
| SpecifyingSystems/FIFO/APMCInnerFIFO | NoError | 1.81 | 0.01 | 325.6x | same |
| SpecifyingSystems/HourClock/APHourClock | NoError | 1.36 | 0.01 | 235.3x | same |
| SpecifyingSystems/HourClock/APHourClock2 | NoError | 1.50 | 0.01 | 126.7x | same |
| SpecifyingSystems/Liveness/APHourClock | NoError | 1.45 | 0.01 | 259.8x | same |
| SpecifyingSystems/Liveness/APLiveHourClock | NoError | 1.45 | 0.01 | 256.8x | same |
| acp/APACP_SB | NoError | 3.31 | 0.01 | 285.6x | same |
| barriers/APBarrier | NoError | 2.08 | 0.01 | 369.3x | same |
| bcastFolklore/APbcastFolklore | NoError | 3.15 | 0.01 | 268.9x | same |
| bosco/APbosco | NoError | 14.98 | 0.05 | 300.1x | same |
| c1cs/APc1cs | NoError | 3.70 | 0.22 | 16.6x | same |
| chang_roberts/APChangRoberts | NoError | 6.30 | 0.01 | 1120.0x | same |
| ewd426/APTokenRing | NoError | 3.57 | 0.02 | 190.3x | same |
| ewd840/APEWD840 | NoError | 2.49 | 0.01 | 441.0x | same |
| ewd840/APSyncTerminationDetection | NoError | 2.40 | 0.01 | 204.7x | same |
| glowingRaccoon/APclean | NoError | 1.66 | 0.01 | 292.4x | same |
| glowingRaccoon/APstages | NoError | 1.73 | 0.01 | 309.4x | same |
| lamport_mutex/APLamportMutex | NoError | 9.57 | 0.01 | 842.0x | same |
| nbacg_guer01/APnbacg_guer01 | NoError | 5.86 | 0.08 | 69.9x | same |
| spanning/APspanning | NoError | 1.97 | 0.01 | 346.2x | same |
| tcp/APtcp | NoError | 13.31 | 0.02 | 535.3x | same |
| transaction_commit/APTCommit | NoError | 2.07 | 0.01 | 367.4x | same |
