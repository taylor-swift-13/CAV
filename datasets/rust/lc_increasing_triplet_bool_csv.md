# LC Increasing Triplet Subsequence Bool CSV

## Problem

Return true if the array contains an increasing subsequence of length three.

## Requirements

- `nums` is a comma-separated list of signed integers.

## Source

- Source: LeetCode problem `increasing-triplet-subsequence`.
- URL: https://leetcode.com/problems/increasing-triplet-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_increasing_triplet_bool_csv(nums: &str) -> bool {
    let mut first = i32::MAX; let mut second = i32::MAX; for p in nums.split(',') { let v = p.parse::<i32>().unwrap(); if v <= first { first = v; } else if v <= second { second = v; } else { return true; } } false
}
```
