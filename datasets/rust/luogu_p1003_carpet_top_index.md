# Luogu P1003 Carpet Top Index

## Problem

Return the topmost carpet covering a query point, or `-1` if none covers it.

## Requirements

- `carpets` is semicolon-separated `x,y,width,height` records.
- Return the 1-based carpet index matching Luogu P1003 order.

## Source

- Source: Luogu problem `P1003`.
- URL: https://www.luogu.com.cn/problem/P1003
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p1003_carpet_top_index(carpets: &str, x: i32, y: i32) -> i32 {
    let mut ans = -1; for (i, rec) in carpets.split(';').enumerate() { let v: Vec<i32> = rec.split(',').map(|p| p.parse::<i32>().unwrap()).collect(); if x >= v[0] && x <= v[0] + v[2] && y >= v[1] && y <= v[1] + v[3] { ans = i as i32 + 1; } } ans
}
```
