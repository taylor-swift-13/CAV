# LC Koko Minimum Speed CSV

## Problem

Return the minimum integer banana-eating speed needed to finish all piles within `h` hours.

## Requirements

- `piles` is a nonempty comma-separated list of positive integers.
- `h` is at least the number of piles.

## Source

- Source: LeetCode problem `koko-eating-bananas`.
- URL: https://leetcode.com/problems/koko-eating-bananas/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_koko_min_speed_csv(piles: &str, h: i32) -> i32 {
    let a: Vec<i32> = piles.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let mut max = 0; for &v in &a { if v > max { max = v; } }
    let mut lo = 1; let mut hi = max;
    while lo < hi { let mid = lo + (hi - lo) / 2; let mut hours = 0; for &v in &a { hours += (v + mid - 1) / mid; } if hours <= h { hi = mid; } else { lo = mid + 1; } }
    lo
}
```
