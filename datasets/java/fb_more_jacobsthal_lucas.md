# fb_more_jacobsthal_lucas

## Problem

Return the `n`th Jacobsthal-Lucas number with `J(0)=2`, `J(1)=1`, and `J(n)=J(n-1)+2*J(n-2)`.

## Requirements

- `1 <= n <= 30`.
- Use only integer arithmetic.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `JacobsthalLucas.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbMoreJacobsthalLucas {
    public static int fb_more_jacobsthal_lucas(int n) {
        int[] dp = new int[n + 1];
        dp[0] = 2; dp[1] = 1;
        for (int i = 2; i <= n; i++) dp[i] = dp[i - 1] + 2 * dp[i - 2];
        return dp[n];
    }
}
```
