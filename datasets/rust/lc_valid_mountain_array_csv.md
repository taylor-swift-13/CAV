# LC Valid Mountain Array CSV

## Problem

Return true if comma-separated array `arr` is a valid mountain array.

## Requirements

- The empty string represents an empty array.
- A valid mountain has length at least `3`, strictly increases, then strictly decreases.

## Source

- Source: LeetCode problem `valid-mountain-array`.
- URL: https://leetcode.com/problems/valid-mountain-array/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_valid_mountain_array_csv(arr: &str) -> bool {
    if arr.is_empty() { return false; }
    let a: Vec<i32> = arr.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let n = a.len();
    if n < 3 { return false; }
    let mut p = 0usize;
    while p + 1 < n && a[p] < a[p + 1] { p += 1; }
    if p == 0 || p == n - 1 { return false; }
    while p + 1 < n && a[p] > a[p + 1] { p += 1; }
    p == n - 1
}
```
