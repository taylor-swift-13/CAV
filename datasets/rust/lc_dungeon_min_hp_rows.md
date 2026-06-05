# LC Dungeon Game Minimum HP Rows

## Problem

Return the minimum initial health needed to rescue the princess.

## Requirements

- Dungeon rows are semicolon-separated comma lists of signed integers.
- Movement is only right or down.

## Source

- Source: LeetCode problem `dungeon-game`.
- URL: https://leetcode.com/problems/dungeon-game/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_dungeon_min_hp_rows(rows: &str) -> i32 {
    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let r = a.len(); let c = a[0].len(); let mut dp = vec![vec![1000000000; c + 1]; r + 1]; dp[r][c - 1] = 1; dp[r - 1][c] = 1; let mut i = r; while i > 0 { i -= 1; let mut j = c; while j > 0 { j -= 1; let need = dp[i + 1][j].min(dp[i][j + 1]) - a[i][j]; dp[i][j] = if need <= 1 { 1 } else { need }; } } dp[0][0]
}
```
