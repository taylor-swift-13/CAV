# fb_binomial_coefficient

## Problem

Return the binomial coefficient `C(n, k)`.

## Requirements

- `0 <= k <= n <= 20`.
- Use integer arithmetic.

## Source

- Source: FormalBenchHF base program `BinomialCoeff.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_binomial_coefficient(n: i32, mut k: i32) -> i32 {
    if k > n - k { k = n - k; }
    let mut c = 1;
    for i in 1..=k { c = c * (n - i + 1) / i; }
    c
}
```
