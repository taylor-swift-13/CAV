# LC Continuous Subarray Sum Bool CSV

## Problem

Return true if a length-at-least-two contiguous subarray has sum divisible by `k`.

## Requirements

- `nums` is a comma-separated list of nonnegative integers.
- `k > 0`.

## Source

- Source: LeetCode problem `continuous-subarray-sum`.
- URL: https://leetcode.com/problems/continuous-subarray-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_continuous_subarray_sum_bool_csv(nums: &str, k: i32) -> bool {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut l = 0usize; while l < a.len() { let mut sum = 0; let mut r = l; while r < a.len() { sum += a[r]; if r > l && sum % k == 0 { return true; } r += 1; } l += 1; } false
}
```
