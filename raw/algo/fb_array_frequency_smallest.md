# fb_array_frequency_smallest

## Problem

Return how many times the smallest value appears in the first `n` elements of `arr`.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FrequencyOfSmallest.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_array_frequency_smallest(int n, int arr[]) {
    if (n == 0) return 0;
    int min = arr[0], count = 1;
    for (int i = 1; i < n; i++) {
        if (min > arr[i]) { min = arr[i]; count = 1; }
        else if (min == arr[i]) count++;
    }
    return count;
}
```
