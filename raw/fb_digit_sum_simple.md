# fb_digit_sum_simple

## Problem

Return the sum of the decimal digits of `n`.

## Requirements

- `0 <= n <= 1000000000`.
- Return `0` when `n` is `0`.

## Source

- Source: FormalBenchHF base program `SumDigits.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_digit_sum_simple(int n) {
    int sum = 0;
    while (n > 0) { sum += n % 10; n /= 10; }
    return sum;
}
```
