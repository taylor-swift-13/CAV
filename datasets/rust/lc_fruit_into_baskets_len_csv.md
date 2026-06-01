# LC Fruit Into Baskets Length CSV

## Problem

Return the longest contiguous subarray containing at most two distinct fruit types.

## Requirements

- `fruits` is a comma-separated list of integer fruit types.

## Source

- Source: LeetCode problem `fruit-into-baskets`.
- URL: https://leetcode.com/problems/fruit-into-baskets/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_fruit_into_baskets_len_csv(fruits: &str) -> i32 {
    let a: Vec<i32> = fruits.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut best = 0; let mut l = 0usize; while l < a.len() { let mut t1 = -1; let mut t2 = -1; let mut r = l; while r < a.len() { if a[r] == t1 || a[r] == t2 { } else if t1 == -1 { t1 = a[r]; } else if t2 == -1 { t2 = a[r]; } else { break; } let len = (r - l + 1) as i32; if len > best { best = len; } r += 1; } l += 1; } best
}
```
