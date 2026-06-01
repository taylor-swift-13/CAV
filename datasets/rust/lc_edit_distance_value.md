# LC Edit Distance Value

## Problem

Return the minimum number of insertions, deletions, and substitutions needed to transform `word1` into `word2`.

## Requirements

- Strings are ASCII.
- Both string lengths are at most `32`.
- Each edit has cost `1`.

## Source

- Source: LeetCode problem `edit-distance`.
- URL: https://leetcode.com/problems/edit-distance/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_edit_distance_value(word1: &str, word2: &str) -> i32 {
    let a = word1.as_bytes();
    let b = word2.as_bytes();
    let n = a.len();
    let m = b.len();
    let mut dp = [[0i32; 33]; 33];
    let mut i = 0usize;
    while i <= n { dp[i][0] = i as i32; i += 1; }
    let mut j = 0usize;
    while j <= m { dp[0][j] = j as i32; j += 1; }
    i = 1;
    while i <= n {
        j = 1;
        while j <= m {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            let mut best = dp[i - 1][j] + 1;
            if dp[i][j - 1] + 1 < best { best = dp[i][j - 1] + 1; }
            if dp[i - 1][j - 1] + cost < best { best = dp[i - 1][j - 1] + cost; }
            dp[i][j] = best;
            j += 1;
        }
        i += 1;
    }
    dp[n][m]
}
```
