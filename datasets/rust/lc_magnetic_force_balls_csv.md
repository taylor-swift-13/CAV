# LC Magnetic Force Between Balls CSV

## Problem

Return the largest minimum distance between any two placed balls.

## Requirements

- `position` is a comma-separated list of basket positions.
- Place exactly `m` balls.

## Source

- Source: LeetCode problem `magnetic-force-between-two-balls`.
- URL: https://leetcode.com/problems/magnetic-force-between-two-balls/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_magnetic_force_balls_csv(position: &str, m: i32) -> i32 {
    let mut a: Vec<i32> = position.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); let mut lo = 1; let mut hi = a[a.len() - 1] - a[0]; let mut ans = 1; while lo <= hi { let mid = lo + (hi - lo) / 2; let mut count = 1; let mut last = a[0]; for &x in a.iter().skip(1) { if x - last >= mid { count += 1; last = x; } } if count >= m { ans = mid; lo = mid + 1; } else { hi = mid - 1; } } ans
}
```
