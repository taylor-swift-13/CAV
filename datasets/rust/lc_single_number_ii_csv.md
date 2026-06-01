# LC Single Number II CSV

## Problem

Return the element that appears once when every other element appears three times.

## Requirements

- `nums` is a comma-separated list of signed integers.

## Source

- Source: LeetCode problem `single-number-ii`.
- URL: https://leetcode.com/problems/single-number-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_single_number_ii_csv(nums: &str) -> i32 {
    let mut ones = 0; let mut twos = 0; for part in nums.split(',') { let v = part.parse::<i32>().unwrap(); ones = (ones ^ v) & !twos; twos = (twos ^ v) & !ones; } ones
}
```
