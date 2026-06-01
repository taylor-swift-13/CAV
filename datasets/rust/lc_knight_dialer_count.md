# LC Knight Dialer Count

## Problem

Return how many distinct phone numbers of length `n` a chess knight can dial, modulo `1_000_000_007`.

## Requirements

- The keypad graph is the standard LeetCode knight dialer keypad.

## Source

- Source: LeetCode problem `knight-dialer`.
- URL: https://leetcode.com/problems/knight-dialer/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_knight_dialer_count(n: i32) -> i32 {
    let moves: Vec<Vec<usize>> = vec![vec![4,6],vec![6,8],vec![7,9],vec![4,8],vec![0,3,9],vec![],vec![0,1,7],vec![2,6],vec![1,3],vec![2,4]]; let modu = 1000000007i64; let mut dp = vec![1i64; 10]; let mut step = 1; while step < n { let mut next = vec![0i64; 10]; let mut i = 0usize; while i < 10 { for &to in &moves[i] { next[to] = (next[to] + dp[i]) % modu; } i += 1; } dp = next; step += 1; } (dp.iter().sum::<i64>() % modu) as i32
}
```
