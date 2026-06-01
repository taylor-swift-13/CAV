# LC Last Stone Weight II CSV

## Problem

Return the smallest possible final stone weight.

## Requirements

- `stones` is a comma-separated list of positive weights.

## Source

- Source: LeetCode problem `last-stone-weight-ii`.
- URL: https://leetcode.com/problems/last-stone-weight-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_last_stone_weight_ii_csv(stones: &str) -> i32 {
    let a: Vec<i32> = stones.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let sum: i32 = a.iter().sum(); let mut dp = vec![0; (sum / 2 + 1) as usize]; for &v in &a { let mut s = sum / 2; while s >= v { let cand = dp[(s - v) as usize] + v; if cand > dp[s as usize] { dp[s as usize] = cand; } s -= 1; } } sum - 2 * dp[(sum / 2) as usize]
}
```
