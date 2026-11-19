# Benchmark

<!-- results -->

Measured on arm64 Darwin 25.5.0, best of 10 runs, wall-clock seconds, with 1 worker and with 8.

| spec | distinct states | TLC | Manyan | speedup | TLC (8) | Manyan (8) | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| closure | 65536 | 2.24 | 0.47 | 4.8x | 0.99 | 0.11 | 9.0x |
| counters | 823543 | 3.55 | 0.68 | 5.2x | 2.88 | 0.19 | 15.0x |
| liveness | 38880 | 4.29 | 0.15 | 28.7x | 2.99 | 0.07 | 40.2x |
| log | 31501 | 0.71 | 0.05 | 13.2x | 0.64 | 0.03 | 23.9x |
| mutex | 11365 | 0.48 | 0.03 | 17.8x | 0.44 | 0.02 | 26.1x |
| partition | 21147 | 0.93 | 0.17 | 5.4x | 0.68 | 0.05 | 13.2x |
| queue | 183680 | 0.95 | 0.16 | 6.0x | 0.85 | 0.06 | 14.2x |
| recursion | 78125 | 1.30 | 0.22 | 5.8x | 0.85 | 0.06 | 14.2x |
| refinement | 30618 | 0.65 | 0.07 | 9.5x | 0.55 | 0.03 | 21.7x |
| symmetry | 21123 | 1.27 | 0.18 | 7.1x | 0.73 | 0.05 | 13.7x |
