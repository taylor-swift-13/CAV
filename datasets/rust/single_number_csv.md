# single_number_csv

## Problem

In a comma-separated integer array where every value appears twice except one, return the single value.

## Requirements

- Input is nonempty.
- Exactly one value appears once and every other value appears twice.
- Values are base-10 integers with no spaces.
- Return the unique value.

## Source

- Source: LeetCode problem `single-number`.
- URL: https://leetcode.com/problems/single-number/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn single_number_csv(nums: &str) -> i32 {
    let mut x = 0;
    for p in nums.split(',') { x ^= p.parse::<i32>().unwrap(); }
    x
}
```
