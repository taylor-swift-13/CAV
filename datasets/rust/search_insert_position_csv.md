# search_insert_position_csv

## Problem

Given a sorted comma-separated integer array `nums`, return the index of `target` or where it should be inserted.

## Requirements

- `nums` is sorted in strictly increasing order.
- The empty string represents an empty array.
- Return the first index whose value is at least `target`.
- If all values are smaller, return the array length.

## Source

- Source: LeetCode problem `search-insert-position`.
- URL: https://leetcode.com/problems/search-insert-position/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn search_insert_position_csv(nums: &str, target: i32) -> i32 {
    if nums.is_empty() { return 0; }
    for (i, p) in nums.split(',').enumerate() { if p.parse::<i32>().unwrap() >= target { return i as i32; } }
    nums.split(',').count() as i32
}
```
