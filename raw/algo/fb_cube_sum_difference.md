# fb_cube_sum_difference

## Problem

Return `(1^3 + 2^3 + ... + n^3) - (1 + 2 + ... + n)`.

## Requirements

- `1 <= n <= 200`.
- Return the signed 32-bit integer result.

## Source

- Source: FormalBenchHF base program `Difference.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_cube_sum_difference(int n) {
    int cubes = 0, linear = 0;
    for (int i = 1; i <= n; i++) { cubes += i * i * i; linear += i; }
    return cubes - linear;
}
```
