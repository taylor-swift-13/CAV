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

```c
int fb_more_paint_fence_ways(int n, int k) {
    int mod = 1000000007;
    int dp[21] = {0};
    dp[0] = 1; dp[1] = k;
    if (n >= 2) dp[2] = k * k;
    for (int i = 3; i <= n; i++) dp[i] = ((k - 1) * (dp[i - 1] + dp[i - 2])) % mod;
    return dp[n];
}
```
