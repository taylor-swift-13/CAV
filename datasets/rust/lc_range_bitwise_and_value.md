# LC Range Bitwise AND Value

## Problem

Return the bitwise AND of all integers in inclusive range `[left, right]`.

## Requirements

- `0 <= left <= right`.

## Source

- Source: LeetCode problem `bitwise-and-of-numbers-range`.
- URL: https://leetcode.com/problems/bitwise-and-of-numbers-range/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_range_bitwise_and_value(mut left: i32, mut right: i32) -> i32 {
    let mut shift = 0; while left < right { left >>= 1; right >>= 1; shift += 1; } left << shift
}
```
