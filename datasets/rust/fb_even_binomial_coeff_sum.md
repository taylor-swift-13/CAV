# fb_even_binomial_coeff_sum

## Problem

Return the FormalBench DP value defined by `dp[0]=1` and `dp[i]=dp[0]+...+dp[i-1]`.

## Requirements

- `0 <= n <= 30`.
- Follow the stated recurrence directly.

## Source

- Source: FormalBenchHF base program `EvenBinomialCoeffSum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_even_binomial_coeff_sum(n: i32) -> i32 {
    let n = n as usize;
    let mut dp = vec![0; n + 1];
    dp[0] = 1;
    for i in 1..=n { for j in 0..i { dp[i] += dp[j]; } }
    dp[n]
}
```
