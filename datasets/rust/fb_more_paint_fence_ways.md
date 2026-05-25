# fb_more_paint_fence_ways

## Problem

Return the FormalBench paint-fence recurrence value for `n` posts and `k` colors.

## Requirements

- `1 <= n <= 20`.
- `1 <= k <= 20`.
- Use modulo `1000000007` in the recurrence.

## Source

- Source: FormalBenchHF base program `CountNoOfWays.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_more_paint_fence_ways(n: i32, k: i32) -> i32 {
    let n = n as usize;
    let mut dp = vec![0; n + 1];
    dp[0] = 1; dp[1] = k;
    if n >= 2 { dp[2] = k * k; }
    for i in 3..=n { dp[i] = ((k - 1) * (dp[i - 1] + dp[i - 2])) % 1000000007; }
    dp[n]
}
```
