# LC Subarray Sum Equals K Count CSV

## Problem

Return how many contiguous subarrays of comma-separated `nums` sum to `k`.

## Requirements

- The empty string represents an empty array.
- The count fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `subarray-sum-equals-k`.
- URL: https://leetcode.com/problems/subarray-sum-equals-k/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_subarray_sum_k_count_csv(nums: &str, k: i32) -> i32 {
    if nums.is_empty() { return 0; }
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let mut count = 0;
    let mut l = 0usize;
    while l < a.len() { let mut sum = 0; let mut r = l; while r < a.len() { sum += a[r]; if sum == k { count += 1; } r += 1; } l += 1; }
    count
}
```
