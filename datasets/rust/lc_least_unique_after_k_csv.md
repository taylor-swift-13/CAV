# LC Least Unique Integers After K Removals CSV

## Problem

Return the fewest distinct integers left after removing exactly `k` elements.

## Requirements

- `arr` is a comma-separated list of integers.

## Source

- Source: LeetCode problem `least-number-of-unique-integers-after-k-removals`.
- URL: https://leetcode.com/problems/least-number-of-unique-integers-after-k-removals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_least_unique_after_k_csv(arr: &str, mut k: i32) -> i32 {
    let a: Vec<i32> = arr.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut freq: Vec<i32> = Vec::new(); let mut i = 0usize; while i < a.len() { let mut seen = false; let mut j = 0usize; while j < i { if a[j] == a[i] { seen = true; } j += 1; } if !seen { let mut c = 0; for &v in &a { if v == a[i] { c += 1; } } freq.push(c); } i += 1; } freq.sort(); let mut left = freq.len() as i32; for f in freq { if k < f { break; } k -= f; left -= 1; } left
}
```
