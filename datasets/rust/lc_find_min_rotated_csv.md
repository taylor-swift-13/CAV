# LC Find Minimum In Rotated Sorted Array CSV

## Problem

Return the minimum value in a rotated sorted array with distinct integers.

## Requirements

- `nums` is a nonempty comma-separated list.
- Values are distinct.

## Source

- Source: LeetCode problem `find-minimum-in-rotated-sorted-array`.
- URL: https://leetcode.com/problems/find-minimum-in-rotated-sorted-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_find_min_rotated_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut l = 0usize; let mut r = a.len() - 1; while l < r { let m = l + (r - l) / 2; if a[m] > a[r] { l = m + 1; } else { r = m; } } a[l]
}
```
