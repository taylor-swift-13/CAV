# LC Minimum Size Subarray Sum Length CSV

## Problem

Return the minimum length of a contiguous subarray with sum at least `target`, or `0` if none exists.

## Requirements

- `nums` is a nonempty comma-separated list of positive integers.
- `target > 0`.

## Source

- Source: LeetCode problem `minimum-size-subarray-sum`.
- URL: https://leetcode.com/problems/minimum-size-subarray-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_subarray_len_csv(target: i32, nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut left = 0usize; let mut sum = 0; let mut best = 1000000;
    let mut right = 0usize; while right < a.len() { sum += a[right]; while sum >= target { let len = (right - left + 1) as i32; if len < best { best = len; } sum -= a[left]; left += 1; } right += 1; } if best == 1000000 { 0 } else { best }
}
```
