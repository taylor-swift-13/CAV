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

```rust
pub fn lc_unique_bst_count(n: i32) -> i32 {
    let mut dp = vec![0; (n + 1) as usize]; dp[0] = 1; let mut nodes = 1; while nodes <= n { let mut root = 1; while root <= nodes { dp[nodes as usize] += dp[(root - 1) as usize] * dp[(nodes - root) as usize]; root += 1; } nodes += 1; } dp[n as usize]
}
```
