# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.20 | 0.47 | 4.7x | 1.02 | 0.12 | 8.7x |
| counters | 823543 | 3.50 | 0.67 | 5.2x | 2.73 | 0.19 | 14.5x |
| liveness | 38880 | 4.18 | 0.18 | 22.8x | 2.81 | 0.09 | 30.2x |
| log | 31501 | 0.70 | 0.05 | 13.6x | 0.59 | 0.02 | 28.3x |
| mutex | 11365 | 0.47 | 0.03 | 17.2x | 0.42 | 0.02 | 25.8x |
| partition | 21147 | 0.90 | 0.17 | 5.2x | 0.68 | 0.05 | 12.4x |
| queue | 183680 | 0.93 | 0.15 | 6.4x | 0.82 | 0.05 | 16.6x |
| recursion | 78125 | 1.20 | 0.22 | 5.4x | 0.83 | 0.06 | 14.2x |
| refinement | 30618 | 0.64 | 0.07 | 9.6x | 0.54 | 0.02 | 22.1x |
| symmetry | 21123 | 1.21 | 0.18 | 6.9x | 0.70 | 0.05 | 14.0x |
