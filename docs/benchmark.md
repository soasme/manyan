# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.19 | 0.48 | 4.6x | 0.95 | 0.12 | 7.8x |
| counters | 823543 | 3.54 | 0.68 | 5.2x | 2.94 | 0.19 | 15.2x |
| liveness | 38880 | 4.32 | 0.14 | 30.1x | 2.93 | 0.07 | 40.2x |
| log | 31501 | 0.66 | 0.05 | 12.4x | 0.58 | 0.02 | 26.3x |
| mutex | 11365 | 0.48 | 0.03 | 16.1x | 0.43 | 0.02 | 24.0x |
| partition | 21147 | 0.93 | 0.17 | 5.5x | 0.68 | 0.05 | 13.1x |
| queue | 183680 | 0.95 | 0.16 | 5.8x | 0.95 | 0.06 | 15.8x |
| recursion | 78125 | 1.23 | 0.22 | 5.5x | 0.87 | 0.06 | 14.4x |
| refinement | 30618 | 0.65 | 0.07 | 9.6x | 0.55 | 0.02 | 22.8x |
| symmetry | 21123 | 1.23 | 0.18 | 6.8x | 0.68 | 0.05 | 13.5x |
