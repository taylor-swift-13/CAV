# LC Maximum Circular Subarray Sum CSV

## Problem

Return the maximum nonempty subarray sum in a circular array.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `maximum-sum-circular-subarray`.
- URL: https://leetcode.com/problems/maximum-sum-circular-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_max_subarray_circular_sum_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut total = a[0]; let mut max_cur = a[0]; let mut max_sum = a[0]; let mut min_cur = a[0]; let mut min_sum = a[0]; let mut i = 1usize; while i < a.len() { let x = a[i]; total += x; max_cur = x.max(max_cur + x); max_sum = max_sum.max(max_cur); min_cur = x.min(min_cur + x); min_sum = min_sum.min(min_cur); i += 1; } if max_sum < 0 { max_sum } else { max_sum.max(total - min_sum) }
}
```
