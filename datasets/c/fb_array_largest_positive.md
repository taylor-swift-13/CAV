# fb_array_largest_positive

## Problem

Return the largest positive value in the first `n` elements of `array`, or `0` if there is none.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `LargestPos.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_array_largest_positive(int array[], int n) {
    int max = 0;
    for (int i = 0; i < n; i++) if (array[i] > 0 && array[i] > max) max = array[i];
    return max;
}
```
