# LC Jump Game CSV

## Problem

Return true if the last index is reachable from index `0` in comma-separated jump lengths.

## Requirements

- The empty string represents an empty array and returns false.
- Each value is nonnegative.

## Source

- Source: LeetCode problem `jump-game`.
- URL: https://leetcode.com/problems/jump-game/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_can_jump_csv(nums: &str) -> bool {
    if nums.is_empty() { return false; }
    let mut reach = 0i32;
    for (i, part) in nums.split(',').enumerate() { let idx = i as i32; if idx > reach { return false; } let v = part.parse::<i32>().unwrap(); if idx + v > reach { reach = idx + v; } }
    true
}
```
