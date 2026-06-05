# fb_easy_next_perfect_square

## Problem

Return the smallest perfect square that is strictly greater than `n`.

## Requirements

- `0 <= n <= 1000000`.
- Return `1` when `n` is `0`.

## Source

- Source: FormalBenchHF base program `NextPerfectSquare.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_easy_next_perfect_square(int n) {
    int i = 1, square = 1;
    while (square <= n) { square = i * i; i++; }
    return square;
}
```
