# Luogu P5740 Best Total Score

## Problem

Return the maximum total score among students encoded as triples `chinese,math,english;...`.

## Requirements

- The empty string returns `0`.
- Scores are nonnegative integers.

## Source

- Source: Luogu problem `P5740`.
- URL: https://www.luogu.com.cn/problem/P5740
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5740_best_total_score(rows: &str) -> i32 {
    if rows.is_empty() { return 0; }
    let mut best = 0;
    for row in rows.split(';') { let vals: Vec<i32> = row.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let total = vals[0] + vals[1] + vals[2]; if total > best { best = total; } }
    best
}
```
