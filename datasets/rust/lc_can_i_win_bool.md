# LC Can I Win Bool

## Problem

Return true if the first player can force a win.

## Requirements

- Players alternately choose unused integers from `1..max_choosable_integer`.
- The player who reaches or exceeds `desired_total` wins.

## Source

- Source: LeetCode problem `can-i-win`.
- URL: https://leetcode.com/problems/can-i-win/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_can_i_win_bool(max_choosable_integer: i32, desired_total: i32) -> bool {
    fn dfs(mask: usize, total: i32, max: i32, target: i32, memo: &mut Vec<i8>) -> bool { if memo[mask] != 0 { return memo[mask] == 1; } let mut i = 0; while i < max { let bit = 1usize << i; if mask & bit == 0 { let pick = i + 1; if total + pick >= target || !dfs(mask | bit, total + pick, max, target, memo) { memo[mask] = 1; return true; } } i += 1; } memo[mask] = -1; false }
    if desired_total <= 0 { return true; } if max_choosable_integer * (max_choosable_integer + 1) / 2 < desired_total { return false; } let mut memo = vec![0i8; 1usize << max_choosable_integer]; dfs(0, 0, max_choosable_integer, desired_total, &mut memo)
}
```
