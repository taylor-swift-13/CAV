# LC Car Fleet Count

## Problem

Return how many car fleets arrive at the target.

## Requirements

- `position` and `speed` are comma-separated lists of equal length.
- Positions are distinct and less than target.

## Source

- Source: LeetCode problem `car-fleet`.
- URL: https://leetcode.com/problems/car-fleet/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_car_fleet_count(target: i32, position: &str, speed: &str) -> i32 {
    let p: Vec<i32> = position.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let s: Vec<i32> = speed.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut cars: Vec<(i32, i32)> = p.into_iter().zip(s.into_iter()).collect(); cars.sort_by(|a, b| b.0.cmp(&a.0)); let mut fleets = 0; let mut slow = -1.0f64; for (pos, spd) in cars { let t = (target - pos) as f64 / spd as f64; if t > slow { fleets += 1; slow = t; } } fleets
}
```
