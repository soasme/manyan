# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.23 | 0.46 | 4.8x | 0.99 | 0.11 | 8.9x |
| counters | 823543 | 3.68 | 0.73 | 5.0x | 2.89 | 0.21 | 13.7x |
| liveness | 38880 | 4.46 | 0.18 | 24.2x | 2.97 | 0.09 | 33.1x |
| log | 31501 | 0.67 | 0.05 | 13.2x | 0.58 | 0.02 | 26.8x |
| mutex | 11365 | 0.49 | 0.03 | 17.7x | 0.44 | 0.02 | 26.5x |
| partition | 21147 | 0.94 | 0.17 | 5.5x | 0.71 | 0.05 | 13.7x |
| queue | 183680 | 1.04 | 0.17 | 6.3x | 1.02 | 0.06 | 16.0x |
| recursion | 78125 | 1.32 | 0.22 | 5.9x | 1.07 | 0.06 | 16.9x |
| refinement | 30618 | 0.71 | 0.08 | 8.9x | 0.65 | 0.03 | 20.9x |
| symmetry | 21123 | 1.51 | 0.19 | 8.1x | 0.97 | 0.06 | 15.9x |
