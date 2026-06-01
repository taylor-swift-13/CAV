# Luogu P5741 Rival Pair Count

## Problem

Given semicolon-separated student score triples, count pairs whose three subject differences are all at most 5 and total-score difference is at most 10.

## Requirements

- Each record is `name:chinese,math,english`.
- Names are ignored for the count.
- There are at most 128 records.

## Source

- Source: Luogu problem `P5741`.
- URL: https://www.luogu.com.cn/problem/P5741
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5741_rival_pair_count(students: &str) -> i32 {
    let mut s: Vec<[i32; 3]> = Vec::new();
    for row in students.split(';') { let scores = row.split(':').nth(1).unwrap(); let vals: Vec<i32> = scores.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); s.push([vals[0], vals[1], vals[2]]); }
    let mut ans = 0;
    let mut a = 0usize; while a < s.len() { let mut b = a + 1; while b < s.len() { let mut ok = true; let mut suma = 0; let mut sumb = 0; let mut k = 0usize; while k < 3 { if (s[a][k] - s[b][k]).abs() > 5 { ok = false; } suma += s[a][k]; sumb += s[b][k]; k += 1; } if ok && (suma - sumb).abs() <= 10 { ans += 1; } b += 1; } a += 1; }
    ans
}
```
