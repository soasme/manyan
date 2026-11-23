# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.24 | 0.48 | 4.7x | 0.98 | 0.13 | 7.3x |
| counters | 823543 | 3.75 | 0.68 | 5.5x | 2.86 | 0.18 | 15.5x |
| liveness | 38880 | 4.53 | 0.15 | 30.8x | 3.06 | 0.08 | 39.2x |
| log | 31501 | 0.68 | 0.05 | 12.6x | 0.59 | 0.02 | 25.5x |
| mutex | 11365 | 0.49 | 0.03 | 17.2x | 0.44 | 0.02 | 24.4x |
| partition | 21147 | 0.91 | 0.18 | 5.1x | 0.69 | 0.07 | 10.3x |
| queue | 183680 | 1.03 | 0.16 | 6.6x | 0.92 | 0.06 | 15.4x |
| recursion | 78125 | 1.28 | 0.24 | 5.4x | 0.93 | 0.07 | 13.2x |
| refinement | 30618 | 0.70 | 0.07 | 9.6x | 0.61 | 0.03 | 21.2x |
| symmetry | 21123 | 1.29 | 0.19 | 6.8x | 0.75 | 0.06 | 12.8x |
