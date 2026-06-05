# Luogu P1047 Remaining Trees

## Problem

Return how many integer tree positions remain after removing all interval-covered positions.

## Requirements

- The road has tree positions from `0` through `length`, inclusive.
- `intervals` is semicolon-separated `left,right` records with inclusive endpoints.

## Source

- Source: Luogu problem `P1047`.
- URL: https://www.luogu.com.cn/problem/P1047
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p1047_remaining_trees(length: i32, intervals: &str) -> i32 {
    let mut removed = vec![false; length as usize + 1]; for rec in intervals.split(';') { let p: Vec<usize> = rec.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); let mut x = p[0]; while x <= p[1] && x <= length as usize { removed[x] = true; x += 1; } } removed.iter().filter(|&&x| !x).count() as i32
}
```
