# LC Product Except Self Sum CSV

## Problem

Compute product-except-self for each comma-separated integer and return the sum of the output array.

## Requirements

- `nums` is nonempty.
- No division is used.
- Intermediate products fit in signed 32-bit integer range.

## Source

- Source: LeetCode problem `product-of-array-except-self`.
- URL: https://leetcode.com/problems/product-of-array-except-self/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_product_except_self_sum_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len();
    let mut left = vec![1; n]; let mut right = vec![1; n]; let mut i = 1usize; while i < n { left[i] = left[i - 1] * a[i - 1]; i += 1; } if n > 0 { let mut j = n - 1; while j > 0 { right[j - 1] = right[j] * a[j]; j -= 1; } }
    let mut sum = 0; i = 0; while i < n { sum += left[i] * right[i]; i += 1; }
    sum
}
```
