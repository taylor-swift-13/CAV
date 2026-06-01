# LC Tuple With Same Product Count CSV

## Problem

Return how many ordered tuples have equal pair products.

## Requirements

- `nums` is a comma-separated list of distinct positive integers.

## Source

- Source: LeetCode problem `tuple-with-same-product`.
- URL: https://leetcode.com/problems/tuple-with-same-product/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_tuple_same_product_count_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut prod = Vec::new(); let mut i = 0usize; while i < a.len() { let mut j = i + 1; while j < a.len() { prod.push(a[i] * a[j]); j += 1; } i += 1; } let mut ans = 0; let mut x = 0usize; while x < prod.len() { let mut y = x + 1; while y < prod.len() { if prod[x] == prod[y] { ans += 8; } y += 1; } x += 1; } ans
}
```
