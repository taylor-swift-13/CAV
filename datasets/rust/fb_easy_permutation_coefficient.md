# fb_easy_permutation_coefficient

## Problem

Return `nPk`, the number of ordered selections of `k` items from `n` items.

## Requirements

- `0 <= k <= n <= 12`.
- Use integer arithmetic.

## Source

- Source: FormalBenchHF base program `PermutationCoefficient.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_permutation_coefficient(n: i32, k: i32) -> i32 {
    let mut res = 1;
    for i in 1..=k { res *= n - i + 1; }
    res
}
```
