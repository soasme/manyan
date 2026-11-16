# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.18 | 0.45 | 4.8x | 0.99 | 0.11 | 9.4x |
| counters | 823543 | 3.44 | 0.67 | 5.1x | 2.81 | 0.19 | 14.8x |
| liveness | 38880 | 4.23 | 0.18 | 24.1x | 2.95 | 0.09 | 34.1x |
| log | 31501 | 0.65 | 0.05 | 12.8x | 0.57 | 0.02 | 27.3x |
| mutex | 11365 | 0.47 | 0.03 | 16.0x | 0.43 | 0.02 | 23.3x |
| partition | 21147 | 0.97 | 0.17 | 5.8x | 0.66 | 0.05 | 13.4x |
| queue | 183680 | 0.93 | 0.15 | 6.2x | 0.84 | 0.05 | 16.8x |
| recursion | 78125 | 1.22 | 0.23 | 5.4x | 0.88 | 0.06 | 13.8x |
| refinement | 30618 | 0.68 | 0.07 | 9.8x | 0.57 | 0.03 | 22.2x |
| symmetry | 21123 | 1.26 | 0.19 | 6.6x | 0.85 | 0.06 | 15.2x |
