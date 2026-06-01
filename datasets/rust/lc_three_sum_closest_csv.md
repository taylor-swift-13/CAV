# LC 3Sum Closest CSV

## Problem

Return the sum of three integers in `nums` closest to `target`.

## Requirements

- `nums` contains at least three integers.
- There is exactly one closest answer in supplied tests.

## Source

- Source: LeetCode problem `3sum-closest`.
- URL: https://leetcode.com/problems/3sum-closest/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_three_sum_closest_csv(nums: &str, target: i32) -> i32 {
    let mut a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); let mut best = a[0] + a[1] + a[2]; let mut i = 0usize; while i + 2 < a.len() { let mut l = i + 1; let mut r = a.len() - 1; while l < r { let sum = a[i] + a[l] + a[r]; if (sum - target).abs() < (best - target).abs() { best = sum; } if sum < target { l += 1; } else { r -= 1; } } i += 1; } best
}
```
