# fb_sum_odd_factors

## Problem

Return the sum of all positive odd divisors of `n`.

## Requirements

- `1 <= n <= 10000`.
- Count each divisor once.

## Source

- Source: FormalBenchHF base program `SumOfOddFactors.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_sum_odd_factors(int n) {
    int sum = 0;
    for (int i = 1; i <= n; i++) if (n % i == 0 && i % 2 == 1) sum += i;
    return sum;
}
```
