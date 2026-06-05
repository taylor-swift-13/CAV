# fb_array_odd_xor_pair_count

## Problem

Return how many unordered pairs have an odd bitwise XOR.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FindOddPair.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_array_odd_xor_pair_count(int a[], int n) {
    int count = 0;
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if ((a[i] ^ a[j]) % 2 == 1) count++;
    return count;
}
```
