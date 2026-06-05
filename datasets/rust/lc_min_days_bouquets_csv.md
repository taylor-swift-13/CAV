# LC Minimum Days Bouquets CSV

## Problem

Return the minimum day needed to make `m` bouquets of `k` adjacent flowers, or `-1` if impossible.

## Requirements

- `bloom_day` is a comma-separated list of positive days.

## Source

- Source: LeetCode problem `minimum-number-of-days-to-make-m-bouquets`.
- URL: https://leetcode.com/problems/minimum-number-of-days-to-make-m-bouquets/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_days_bouquets_csv(bloom_day: &str, m: i32, k: i32) -> i32 {
    let a: Vec<i32> = bloom_day.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); if (m * k) as usize > a.len() { return -1; } let mut lo = *a.iter().min().unwrap(); let mut hi = *a.iter().max().unwrap(); while lo < hi { let mid = lo + (hi - lo) / 2; let mut made = 0; let mut run = 0; for &v in &a { if v <= mid { run += 1; if run == k { made += 1; run = 0; } } else { run = 0; } } if made >= m { hi = mid; } else { lo = mid + 1; } } lo
}
```
