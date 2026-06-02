# fb_first_digit_factorial

## Problem

Return the first decimal digit of `n!`.

## Requirements

- `1 <= n <= 10`.
- Compute the factorial using integer arithmetic.

## Source

- Source: FormalBenchHF base program `FirstDigit.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_first_digit_factorial(int n) {
    int fact = 1;
    for (int i = 2; i <= n; i++) fact *= i;
    int first = 0;
    while (fact > 0) { first = fact % 10; fact /= 10; }
    return first;
}
```
