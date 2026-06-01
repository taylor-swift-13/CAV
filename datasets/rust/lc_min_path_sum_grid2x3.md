# LC Min Path Sum 2x3

## Problem

Return the minimum path sum from top-left to bottom-right in a 2x3 grid moving only right or down.

## Requirements

- Grid values are supplied row-major.
- All values are nonnegative.

## Source

- Source: LeetCode problem `minimum-path-sum`.
- URL: https://leetcode.com/problems/minimum-path-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_path_sum_grid2x3(a00: i32, a01: i32, a02: i32, a10: i32, a11: i32, a12: i32) -> i32 {
    let d00 = a00;
    let d01 = d00 + a01;
    let d02 = d01 + a02;
    let d10 = d00 + a10;
    let d11 = if d01 < d10 { d01 } else { d10 } + a11;
    let d12 = if d02 < d11 { d02 } else { d11 } + a12;
    d12
}
```
