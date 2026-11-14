# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.17 | 0.46 | 4.7x | 0.93 | 0.11 | 8.4x |
| counters | 823543 | 3.45 | 0.70 | 4.9x | 2.76 | 0.21 | 13.4x |
| liveness | 38880 | 4.20 | 0.17 | 24.1x | 2.83 | 0.17 | 17.1x |
| log | 31501 | 0.65 | 0.05 | 13.4x | 0.56 | 0.03 | 19.8x |
| mutex | 11365 | 0.47 | 0.03 | 17.4x | 0.42 | 0.02 | 17.9x |
| partition | 21147 | 0.90 | 0.17 | 5.4x | 0.65 | 0.06 | 11.6x |
| queue | 183680 | 0.93 | 0.15 | 6.2x | 0.81 | 0.06 | 13.7x |
| recursion | 78125 | 1.20 | 0.22 | 5.4x | 0.84 | 0.07 | 12.3x |
| refinement | 30618 | 0.64 | 0.07 | 9.4x | 0.53 | 0.03 | 16.9x |
| symmetry | 21123 | 1.22 | 0.18 | 6.7x | 0.68 | 0.06 | 12.3x |
