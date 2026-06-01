# LC Dice Rolls With Target Sum

## Problem

Return how many ways `n` dice with faces `1..k` sum to `target`, modulo `1_000_000_007`.

## Requirements

- `n`, `k`, and `target` are nonnegative and small in supplied tests.

## Source

- Source: LeetCode problem `number-of-dice-rolls-with-target-sum`.
- URL: https://leetcode.com/problems/number-of-dice-rolls-with-target-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_num_dice_rolls_target(n: i32, k: i32, target: i32) -> i32 {
    let modu = 1000000007i64; let t = target as usize; let mut dp = vec![0i64; t + 1]; dp[0] = 1; let mut d = 0; while d < n { let mut next = vec![0i64; t + 1]; let mut s = 0usize; while s <= t { if dp[s] != 0 { let mut f = 1; while f <= k && s + f as usize <= t { next[s + f as usize] = (next[s + f as usize] + dp[s]) % modu; f += 1; } } s += 1; } dp = next; d += 1; } dp[t] as i32
}
```
