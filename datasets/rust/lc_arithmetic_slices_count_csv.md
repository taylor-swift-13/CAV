# LC Arithmetic Slices Count CSV

## Problem

Return how many contiguous arithmetic subarrays of length at least 3 exist.

## Requirements

- `nums` is a nonempty comma-separated list of integers.

## Source

- Source: LeetCode problem `arithmetic-slices`.
- URL: https://leetcode.com/problems/arithmetic-slices/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_arithmetic_slices_count_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut cur = 0; let mut ans = 0; let mut i = 2usize; while i < a.len() { if a[i] - a[i - 1] == a[i - 1] - a[i - 2] { cur += 1; } else { cur = 0; } ans += cur; i += 1; } ans
}
```
