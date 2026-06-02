# fb_array_max_subarray_length

## Problem

Return the length of the contiguous subarray with the largest positive running sum, following the FormalBench zero-baseline scan.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `MaxSubArraySum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_array_max_subarray_length(int a[], int size) {
    int best = 0, cur = 0, start = 0, end = 0, s = 0;
    for (int i = 0; i < size; i++) {
        cur += a[i];
        if (best < cur) { best = cur; start = s; end = i; }
        if (cur < 0) { cur = 0; s = i + 1; }
    }
    return end - start + 1;
}
```
