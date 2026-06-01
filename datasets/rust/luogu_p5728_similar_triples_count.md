# Luogu P5728 Similar Triples Count

## Problem

Count pairs of students whose three subject scores differ by at most 5 each and total scores differ by at most 10.

## Requirements

- Rows are encoded as `a,b,c;a,b,c;...`.
- The empty string returns `0`.

## Source

- Source: Luogu problem `P5728`.
- URL: https://www.luogu.com.cn/problem/P5728
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5728_similar_triples_count(rows: &str) -> i32 {
    if rows.is_empty() { return 0; }
    let a: Vec<Vec<i32>> = rows.split(';').map(|row| row.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect();
    let mut count = 0;
    let mut x = 0usize; while x < a.len() { let mut y = x + 1; while y < a.len() { let mut ok = true; let mut k = 0usize; while k < 3 { let mut d = a[x][k] - a[y][k]; if d < 0 { d = -d; } if d > 5 { ok = false; } k += 1; } let tx = a[x][0] + a[x][1] + a[x][2]; let ty = a[y][0] + a[y][1] + a[y][2]; let mut td = tx - ty; if td < 0 { td = -td; } if ok && td <= 10 { count += 1; } y += 1; } x += 1; }
    count
}
```
