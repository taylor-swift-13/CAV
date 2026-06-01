# LC Maximum Length Of Repeated Subarray

## Problem

Return the maximum length of a subarray appearing in both arrays.

## Requirements

- Arrays are comma-separated integer lists.

## Source

- Source: LeetCode problem `maximum-length-of-repeated-subarray`.
- URL: https://leetcode.com/problems/maximum-length-of-repeated-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_repeated_subarray_max_len(nums1: &str, nums2: &str) -> i32 {
    let a: Vec<i32> = nums1.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let b: Vec<i32> = nums2.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut dp = vec![vec![0; b.len() + 1]; a.len() + 1]; let mut best = 0; let mut i = 1usize; while i <= a.len() { let mut j = 1usize; while j <= b.len() { if a[i - 1] == b[j - 1] { dp[i][j] = dp[i - 1][j - 1] + 1; if dp[i][j] > best { best = dp[i][j]; } } j += 1; } i += 1; } best
}
```
