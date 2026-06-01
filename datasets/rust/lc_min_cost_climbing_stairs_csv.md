# LC Min Cost Climbing Stairs CSV

## Problem

Return the minimum cost to reach the top of the staircase.

## Requirements

- `cost` is a comma-separated list of nonnegative integers.
- You may start at step 0 or step 1.

## Source

- Source: LeetCode problem `min-cost-climbing-stairs`.
- URL: https://leetcode.com/problems/min-cost-climbing-stairs/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_cost_climbing_stairs_csv(cost: &str) -> i32 {
    let a: Vec<i32> = cost.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut p2 = 0; let mut p1 = 0; let mut i = 2usize; while i <= a.len() { let x = p1 + a[i - 1]; let y = p2 + a[i - 2]; let cur = if x < y { x } else { y }; p2 = p1; p1 = cur; i += 1; } p1
}
```
