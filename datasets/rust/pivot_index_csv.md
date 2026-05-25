# pivot_index_csv

## Problem

Return the leftmost pivot index of comma-separated integer array `nums`, or `-1` if none exists.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string has no pivot and returns `-1`.
- A pivot has equal sum strictly to its left and strictly to its right.
- Return the leftmost pivot index.

## Source

- Source: LeetCode problem `find-pivot-index`.
- URL: https://leetcode.com/problems/find-pivot-index/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn pivot_index_csv(nums: &str) -> i32 {
    if nums.is_empty() { return -1; }
    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let total: i32 = values.iter().sum(); let mut left = 0;
    for i in 0..values.len() { if left == total - left - values[i] { return i as i32; } left += values[i]; }
    -1
}
```
