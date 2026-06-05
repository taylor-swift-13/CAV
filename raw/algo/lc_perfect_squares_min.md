# LC Perfect Squares Min

## Problem

Return the least number of perfect squares whose sum is `n`.

## Requirements

- `1 <= n <= 2000`.
- The answer fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `perfect-squares`.
- URL: https://leetcode.com/problems/perfect-squares/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_perfect_squares_min(int n) {
    int dp[2001]; for (int i = 0; i <= n; i++) dp[i] = 1000000; dp[0] = 0;
    for (int i = 1; i * i <= n; i++) { int sq = i * i; for (int s = sq; s <= n; s++) if (dp[s - sq] + 1 < dp[s]) dp[s] = dp[s - sq] + 1; }
    return dp[n];
}
```
