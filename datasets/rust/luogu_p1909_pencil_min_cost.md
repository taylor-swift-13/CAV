# Luogu P1909 Pencil Min Cost

## Problem

Return the minimum cost to buy at least `n` pencils.

## Requirements

- `options` is semicolon-separated `pack_size,price` records.
- Each purchase uses only one supplier option.

## Source

- Source: Luogu problem `P1909`.
- URL: https://www.luogu.com.cn/problem/P1909
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p1909_pencil_min_cost(n: i32, options: &str) -> i32 {
    let mut best = i32::MAX; for rec in options.split(';') { let p: Vec<i32> = rec.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); best = best.min(((n + p[0] - 1) / p[0]) * p[1]); } best
}
```
