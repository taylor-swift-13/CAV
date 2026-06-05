# LC Maximum Subarray Sum CSV

## Problem

Return the maximum sum over all nonempty contiguous subarrays.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `maximum-subarray`.
- URL: https://leetcode.com/problems/maximum-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_max_subarray_sum_csv(nums: &str) -> i32 {
    let mut best = i32::MIN; let mut cur = 0; for part in nums.split(',') { let v = part.parse::<i32>().unwrap(); cur = if cur < 0 { v } else { cur + v }; if cur > best { best = cur; } } best
}
```
