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

```rust
pub fn sg_prime_check_flag(n: i32) -> bool {
    if n < 2 { return false; }
    let mut d = 2;
    while d * d <= n { if n % d == 0 { return false; } d += 1; }
    true
}
```
