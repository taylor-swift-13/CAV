# LC Count Number Of Nice Subarrays CSV

## Problem

Return how many contiguous subarrays contain exactly `k` odd numbers.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `count-number-of-nice-subarrays`.
- URL: https://leetcode.com/problems/count-number-of-nice-subarrays/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_nice_subarrays_count_csv(nums: &str, k: i32) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut ans = 0; let mut l = 0usize; while l < a.len() { let mut odds = 0; let mut r = l; while r < a.len() { if a[r] % 2 == 1 { odds += 1; } if odds == k { ans += 1; } r += 1; } l += 1; } ans
}
```
