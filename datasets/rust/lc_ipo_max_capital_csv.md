# LC IPO Max Capital CSV

## Problem

Return maximized capital after selecting at most `k` projects.

## Requirements

- `profits` and `capital` are comma-separated arrays of equal length.
- Each project can be selected at most once.

## Source

- Source: LeetCode problem `ipo`.
- URL: https://leetcode.com/problems/ipo/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_ipo_max_capital_csv(k: i32, mut w: i32, profits: &str, capital: &str) -> i32 {
    let p: Vec<i32> = profits.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let c: Vec<i32> = capital.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut used = vec![false; p.len()]; let mut step = 0; while step < k { let mut best: Option<usize> = None; let mut i = 0usize; while i < p.len() { if !used[i] && c[i] <= w && (best.is_none() || p[i] > p[best.unwrap()]) { best = Some(i); } i += 1; } if let Some(b) = best { used[b] = true; w += p[b]; } else { break; } step += 1; } w
}
```
