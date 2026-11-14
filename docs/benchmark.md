# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.16 | 0.46 | 4.7x | 0.93 | 0.11 | 8.2x |
| counters | 823543 | 3.46 | 0.70 | 5.0x | 3.02 | 0.21 | 14.5x |
| liveness | 38880 | 4.19 | 0.17 | 24.2x | 2.91 | 0.16 | 17.7x |
| log | 31501 | 0.64 | 0.05 | 13.1x | 0.58 | 0.03 | 20.5x |
| mutex | 11365 | 0.47 | 0.03 | 17.7x | 0.41 | 0.02 | 17.7x |
| partition | 21147 | 0.90 | 0.17 | 5.4x | 0.67 | 0.06 | 11.9x |
| queue | 183680 | 0.93 | 0.15 | 6.3x | 0.81 | 0.06 | 13.8x |
| recursion | 78125 | 1.19 | 0.22 | 5.5x | 0.82 | 0.06 | 12.8x |
| refinement | 30618 | 0.64 | 0.07 | 9.6x | 0.54 | 0.03 | 17.1x |
| symmetry | 21123 | 1.22 | 0.17 | 7.0x | 0.67 | 0.05 | 12.4x |
