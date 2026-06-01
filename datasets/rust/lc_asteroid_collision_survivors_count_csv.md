# LC Asteroid Collision Survivors Count CSV

## Problem

Simulate asteroid collisions and return the number of surviving asteroids.

## Requirements

- `asteroids` is a comma-separated list of nonzero integers.
- Positive moves right and negative moves left.

## Source

- Source: LeetCode problem `asteroid-collision`.
- URL: https://leetcode.com/problems/asteroid-collision/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_asteroid_collision_survivors_count_csv(asteroids: &str) -> i32 {
    let mut st: Vec<i32> = Vec::new(); for part in asteroids.split(',') { let v = part.parse::<i32>().unwrap(); let mut alive = true; while alive && v < 0 && !st.is_empty() && *st.last().unwrap() > 0 { let last = *st.last().unwrap(); if last < -v { st.pop(); } else if last == -v { st.pop(); alive = false; } else { alive = false; } } if alive { st.push(v); } } st.len() as i32
}
```
