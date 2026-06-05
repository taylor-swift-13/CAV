# fb_factorial_last_two_digits

## Problem

Return the last two decimal digits of `n!`.

## Requirements

- `1 <= n <= 12`.
- Compute the factorial using signed 32-bit integer arithmetic.

## Source

- Source: FormalBenchHF base program `LastTwoDigits.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_factorial_last_two_digits(int n) {
    int factorial = 1;
    for (int i = 1; i <= n; i++) factorial *= i;
    return factorial % 100;
}
```
