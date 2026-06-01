# LC Ship Capacity Within Days CSV

## Problem

Return the minimum ship capacity needed to deliver all weights within `days` days.

## Requirements

- `weights` is a comma-separated list of positive package weights.

## Source

- Source: LeetCode problem `capacity-to-ship-packages-within-d-days`.
- URL: https://leetcode.com/problems/capacity-to-ship-packages-within-d-days/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_ship_capacity_days_csv(weights: &str, days: i32) -> i32 {
    let a: Vec<i32> = weights.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut lo = *a.iter().max().unwrap(); let mut hi: i32 = a.iter().sum(); while lo < hi { let mid = lo + (hi - lo) / 2; let mut need = 1; let mut load = 0; for &v in &a { if load + v > mid { need += 1; load = 0; } load += v; } if need <= days { hi = mid; } else { lo = mid + 1; } } lo
}
```
