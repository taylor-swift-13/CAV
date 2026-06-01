# Luogu P5742 Excellent Count

## Problem

Count students satisfying Luogu P5742's excellent condition.

## Requirements

- Rows are encoded as `id,academic,quality;...`.
- A student is excellent if `academic + quality > 140` and `7*academic + 3*quality >= 800`.

## Source

- Source: Luogu problem `P5742`.
- URL: https://www.luogu.com.cn/problem/P5742
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5742_excellent_count(rows: &str) -> i32 {
    let mut ans = 0; for row in rows.split(';') { let p: Vec<i32> = row.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let a = p[1]; let q = p[2]; if a + q > 140 && 7 * a + 3 * q >= 800 { ans += 1; } } ans
}
```
