# LC Find Duplicate Number CSV

## Problem

Return the duplicated number in comma-separated `nums`.

## Requirements

- `nums` has length `n+1` and values in `1..n`.
- At least one duplicate exists.

## Source

- Source: LeetCode problem `find-the-duplicate-number`.
- URL: https://leetcode.com/problems/find-the-duplicate-number/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_find_duplicate_number_csv(nums: &str) -> i32 {
    let mut seen = vec![false; 2048]; for part in nums.split(',') { let v = part.parse::<usize>().unwrap(); if seen[v] { return v as i32; } seen[v] = true; } -1
}
```
