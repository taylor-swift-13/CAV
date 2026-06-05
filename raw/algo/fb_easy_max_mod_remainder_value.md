# fb_easy_max_mod_remainder_value

## Problem

Return the largest integer `i` in `[1, n]` such that `i % x == y`, or `0` if no such value exists.

## Requirements

- `1 <= n <= 10000`.
- `1 <= x <= 1000`.
- `0 <= y < x`.

## Source

- Source: FormalBenchHF base program `FindMaxVal.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_easy_max_mod_remainder_value(int n, int x, int y) {
    int max = 0;
    for (int i = 1; i <= n; i++) if (i % x == y) max = i;
    return max;
}
```
