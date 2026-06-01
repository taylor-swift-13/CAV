# LC Maximum Product Of Three Numbers CSV

## Problem

Return the maximum product of any three integers in comma-separated `nums`.

## Requirements

- `nums` contains at least three integers.
- The result fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `maximum-product-of-three-numbers`.
- URL: https://leetcode.com/problems/maximum-product-of-three-numbers/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_max_product_three_csv(nums: &str) -> i32 {
    let mut a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); let n = a.len(); let p1 = a[n - 1] * a[n - 2] * a[n - 3]; let p2 = a[n - 1] * a[0] * a[1]; if p1 > p2 { p1 } else { p2 }
}
```
