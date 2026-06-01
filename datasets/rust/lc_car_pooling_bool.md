# LC Car Pooling Bool

## Problem

Return true if all trips can be served without exceeding capacity.

## Requirements

- Trips are encoded as `passengers,from,to;...`.
- Locations are nonnegative integers.

## Source

- Source: LeetCode problem `car-pooling`.
- URL: https://leetcode.com/problems/car-pooling/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_car_pooling_bool(trips: &str, capacity: i32) -> bool {
    let mut diff = vec![0; 1001]; for row in trips.split(';') { let p: Vec<usize> = row.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); diff[p[1]] += p[0] as i32; diff[p[2]] -= p[0] as i32; } let mut load = 0; for x in diff { load += x; if load > capacity { return false; } } true
}
```
