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

```c
int fb_even_binomial_coeff_sum(int n) {
    int dp[31] = {0};
    dp[0] = 1;
    for (int i = 1; i <= n; i++) {
        for (int j = 0; j < i; j++) dp[i] += dp[j];
    }
    return dp[n];
}
```
