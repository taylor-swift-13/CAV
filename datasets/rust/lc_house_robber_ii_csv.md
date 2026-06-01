# LC House Robber II CSV

## Problem

Return the maximum amount that can be robbed from circularly arranged houses.

## Requirements

- `nums` is a nonempty comma-separated list of nonnegative integers.
- Adjacent houses in the circle cannot both be robbed.

## Source

- Source: LeetCode problem `house-robber-ii`.
- URL: https://leetcode.com/problems/house-robber-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_house_robber_ii_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); if a.len() == 1 { return a[0]; }
    fn rob(slice: &[i32]) -> i32 { let mut prev = 0; let mut cur = 0; for &v in slice { let next = if prev + v > cur { prev + v } else { cur }; prev = cur; cur = next; } cur }
    let a1 = rob(&a[0..a.len()-1]); let a2 = rob(&a[1..]); if a1 > a2 { a1 } else { a2 }
}
```
