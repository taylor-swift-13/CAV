# LC Maximum Erasure Value CSV

## Problem

Return the maximum sum of a subarray with all distinct elements.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `maximum-erasure-value`.
- URL: https://leetcode.com/problems/maximum-erasure-value/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_maximum_erasure_value_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut best = 0; let mut l = 0usize; while l < a.len() { let mut sum = 0; let mut ok = true; let mut r = l; while r < a.len() && ok { let mut t = l; while t < r { if a[t] == a[r] { ok = false; } t += 1; } if ok { sum += a[r]; if sum > best { best = sum; } } r += 1; } l += 1; } best
}
```
