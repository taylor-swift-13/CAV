# LC Unique Binary Search Trees Count

## Problem

Return how many structurally unique BSTs can store values `1..n`.

## Requirements

- `0 <= n <= 19`.
- This is the Catalan-number DP used by the original problem.

## Source

- Source: LeetCode problem `unique-binary-search-trees`.
- URL: https://leetcode.com/problems/unique-binary-search-trees/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_unique_bst_count(int n) {
    int dp[20] = {0}; dp[0] = 1;
    for (int nodes = 1; nodes <= n; nodes++) for (int root = 1; root <= nodes; root++) dp[nodes] += dp[root - 1] * dp[nodes - root];
    return dp[n];
}
```
