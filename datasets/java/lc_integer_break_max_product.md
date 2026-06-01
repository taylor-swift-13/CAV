# LC Integer Break Max Product

## Problem

Break `n` into at least two positive integers and return the maximum product.

## Requirements

- `2 <= n <= 58`.
- The answer fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `integer-break`.
- URL: https://leetcode.com/problems/integer-break/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcIntegerBreakMaxProduct {
    public static int lc_integer_break_max_product(int n) {
        int[] dp = new int[n + 1]; dp[1] = 1; for (int i = 2; i <= n; i++) for (int j = 1; j < i; j++) dp[i] = Math.max(dp[i], Math.max(j, dp[j]) * Math.max(i - j, dp[i - j])); return dp[n];
    }
}
```
