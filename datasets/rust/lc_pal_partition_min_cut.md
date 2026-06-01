# LC Palindrome Partitioning II Min Cut

## Problem

Return the minimum cuts needed so every substring part is a palindrome.

## Requirements

- `s` contains lowercase English letters.

## Source

- Source: LeetCode problem `palindrome-partitioning-ii`.
- URL: https://leetcode.com/problems/palindrome-partitioning-ii/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_pal_partition_min_cut(s: &str) -> i32 {
    let b = s.as_bytes(); let n = b.len(); let mut pal = vec![vec![false; n]; n]; let mut cut: Vec<i32> = (0..n as i32).collect(); let mut r = 0usize; while r < n { let mut l = r + 1; while l > 0 { l -= 1; if b[l] == b[r] && (r - l < 2 || pal[l + 1][r - 1]) { pal[l][r] = true; if l == 0 { cut[r] = 0; } else if cut[l - 1] + 1 < cut[r] { cut[r] = cut[l - 1] + 1; } } } r += 1; } cut[n - 1]
}
```
