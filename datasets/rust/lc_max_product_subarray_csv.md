# LC Maximum Product Subarray CSV

## Problem

Return the maximum product of a nonempty contiguous subarray.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `maximum-product-subarray`.
- URL: https://leetcode.com/problems/maximum-product-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_max_product_subarray_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut maxp = a[0]; let mut minp = a[0]; let mut best = a[0]; let mut i = 1usize; while i < a.len() { let x = a[i]; if x < 0 { let t = maxp; maxp = minp; minp = t; } maxp = x.max(maxp * x); minp = x.min(minp * x); if maxp > best { best = maxp; } i += 1; } best
}
```
