# fb_search_min_of_three

## Problem

Return the minimum of integers `a`, `b`, and `c`.

## Requirements

- Inputs are signed 32-bit integers.

## Source

- Source: FormalBenchHF base program `MinOfThree.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_search_min_of_three(int a, int b, int c) {
    int min = a; if (b < min) min = b; if (c < min) min = c; return min;
}
```
