# fb_prime_divisor_sum

## Problem

Return the sum of the distinct prime divisors of `n`.

## Requirements

- `2 <= n <= 10000`.
- Each prime divisor is counted once.

## Source

- Source: FormalBenchHF base program `Sum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_prime_divisor_sum(int n) {
    int sums[10001] = {0};
    for (int i = 2; i <= n; i++) {
        if (sums[i] == 0) {
            for (int j = i; j <= n; j += i) sums[j] += i;
        }
    }
    return sums[n];
}
```
