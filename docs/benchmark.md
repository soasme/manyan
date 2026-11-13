# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.15 | 0.46 | 4.7x | 0.96 | 0.11 | 8.5x |
| counters | 823543 | 3.36 | 0.74 | 4.6x | 2.81 | 0.21 | 13.2x |
| liveness | 38880 | 4.20 | 0.17 | 24.4x | 2.92 | 0.17 | 16.8x |
| log | 31501 | 0.64 | 0.05 | 12.9x | 0.57 | 0.03 | 20.5x |
| mutex | 11365 | 0.47 | 0.03 | 16.9x | 0.42 | 0.02 | 18.1x |
| partition | 21147 | 0.90 | 0.17 | 5.4x | 0.66 | 0.06 | 12.0x |
| queue | 183680 | 0.92 | 0.15 | 6.2x | 0.81 | 0.06 | 13.6x |
| recursion | 78125 | 1.18 | 0.23 | 5.1x | 0.80 | 0.07 | 11.7x |
| refinement | 30618 | 0.64 | 0.07 | 8.8x | 0.56 | 0.03 | 17.3x |
| symmetry | 21123 | 1.21 | 0.18 | 6.8x | 0.69 | 0.05 | 12.9x |
