# fb_sum_even_factors

## Problem

Return the sum of all positive even divisors of `n`, excluding `1`.

## Requirements

- `1 <= n <= 10000`.
- Count each divisor once.

## Source

- Source: FormalBenchHF base program `Sumoffactors.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_sum_even_factors(n: i32) -> i32 {
    let mut sum = 0;
    for i in 2..=n { if n % i == 0 && i % 2 == 0 { sum += i; } }
    sum
}
```
