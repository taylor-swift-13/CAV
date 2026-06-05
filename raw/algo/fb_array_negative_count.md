# fb_array_negative_count

## Problem

Return the number of negative values in the first `n` elements of `array`.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `NegCount.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_array_negative_count(int array[], int n) {
    int count = 0;
    for (int i = 0; i < n; i++) if (array[i] < 0) count++;
    return count;
}
```
