# fb_largest_prime_factor

## Problem

Return the largest prime factor of `n`.

## Requirements

- `2 <= n <= 100000`.
- Return `n` itself when `n` is prime.

## Source

- Source: FormalBenchHF base program `MaxPrimeFactors.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_largest_prime_factor(int n) {
    int max = 0;
    for (int i = 2; i <= n; i++) while (n % i == 0) { max = i; n /= i; }
    return max;
}
```
