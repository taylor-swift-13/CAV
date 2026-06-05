# LC Profitable Schemes Count

## Problem

Return how many subsets of jobs use at most `n` members and earn at least `min_profit`.

## Requirements

- `group` and `profit` are comma-separated lists of equal length.
- Return the count modulo `1_000_000_007`.

## Source

- Source: LeetCode problem `profitable-schemes`.
- URL: https://leetcode.com/problems/profitable-schemes/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_profitable_schemes_count(n: i32, min_profit: i32, group: &str, profit: &str) -> i32 {
    let g: Vec<usize> = group.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); let p: Vec<usize> = profit.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); let nn = n as usize; let mp = min_profit as usize; let modu = 1000000007i32; let mut dp = vec![vec![0i32; mp + 1]; nn + 1]; dp[0][0] = 1; let mut job = 0usize; while job < g.len() { let mut members = nn + 1; while members > g[job] { members -= 1; let mut prof = mp + 1; while prof > 0 { prof -= 1; let prev = prof.saturating_sub(p[job]); dp[members][prof] = (dp[members][prof] + dp[members - g[job]][prev]) % modu; } } job += 1; } let mut ans = 0; let mut members = 0usize; while members <= nn { ans = (ans + dp[members][mp]) % modu; members += 1; } ans
}
```
