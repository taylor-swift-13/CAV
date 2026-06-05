# SpecGenBench Prime Check Flag

## Problem

Return true if `n` is prime.

## Requirements

- `n >= 0`.
- Values less than `2` are not prime.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/PrimeCheck`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/PrimeCheck/PrimeCheck.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sg_prime_check_flag(int n) {
    if (n < 2) return 0;
    for (int d = 2; d * d <= n; d++) if (n % d == 0) return 0;
    return 1;
}
```
