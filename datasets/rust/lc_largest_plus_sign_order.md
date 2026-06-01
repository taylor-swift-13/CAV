# LC Largest Plus Sign Order

## Problem

Return the order of the largest axis-aligned plus sign.

## Requirements

- Mines are encoded as `r,c;...`; use `-` for no mines.
- Grid size is `n x n`.

## Source

- Source: LeetCode problem `order-of-largest-plus-sign`.
- URL: https://leetcode.com/problems/order-of-largest-plus-sign/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_largest_plus_sign_order(n: i32, mines: &str) -> i32 {
    let nn = n as usize; let mut g = vec![vec![1; nn]; nn]; if mines != "-" { for row in mines.split(';') { let p: Vec<usize> = row.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); g[p[0]][p[1]] = 0; } } let mut best = 0; let mut x = 0usize; while x < nn { let mut y = 0usize; while y < nn { if g[x][y] == 1 { let mut order = 1usize; while x >= order && x + order < nn && y >= order && y + order < nn && g[x - order][y] == 1 && g[x + order][y] == 1 && g[x][y - order] == 1 && g[x][y + order] == 1 { order += 1; } if order as i32 > best { best = order as i32; } } y += 1; } x += 1; } best
}
```
