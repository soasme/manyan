# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

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
