# sign_of_product_csv

## Problem

Return the sign of the product of comma-separated integers: `1`, `-1`, or `0`.

## Requirements

- The empty string is treated as an empty product with sign `1`.
- Return `0` if any value is zero.
- Return `-1` for an odd number of negative nonzero values.
- Return `1` otherwise.

## Source

- Source: LeetCode problem `sign-of-the-product-of-an-array`.
- URL: https://leetcode.com/problems/sign-of-the-product-of-an-array/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sign_of_product_csv(nums: &str) -> i32 {
    if nums.is_empty() { return 1; }
    let mut sign = 1;
    for p in nums.split(',') { let v = p.parse::<i32>().unwrap(); if v == 0 { return 0; } if v < 0 { sign = -sign; } }
    sign
}
```
