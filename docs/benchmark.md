# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 3 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.16 | 0.46 | 4.7x | 0.95 | 0.11 | 8.4x |
| counters | 823543 | 3.49 | 0.74 | 4.7x | 2.79 | 0.22 | 12.8x |
| liveness | 38880 | 4.21 | 0.17 | 24.4x | 2.81 | 0.17 | 16.1x |
| log | 31501 | 0.65 | 0.05 | 13.0x | 0.60 | 0.03 | 21.1x |
| mutex | 11365 | 0.47 | 0.03 | 17.2x | 0.44 | 0.02 | 18.5x |
| partition | 21147 | 0.90 | 0.17 | 5.4x | 0.69 | 0.06 | 10.6x |
| queue | 183680 | 0.94 | 0.15 | 6.1x | 0.83 | 0.06 | 12.8x |
| recursion | 78125 | 1.22 | 0.24 | 5.1x | 0.84 | 0.07 | 11.8x |
| refinement | 30618 | 0.64 | 0.07 | 8.6x | 0.57 | 0.04 | 16.0x |
| symmetry | 21123 | 1.23 | 0.18 | 6.7x | 0.70 | 0.06 | 11.4x |
