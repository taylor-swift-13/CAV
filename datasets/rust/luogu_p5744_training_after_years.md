# Luogu P5744 Training After Years

## Problem

After `years` yearly updates, return `age + score` where age increases by 1 each year and score increases by 20 percent capped at 600.

## Requirements

- `years >= 0`.
- Use truncating integer arithmetic after each yearly score update.

## Source

- Source: Luogu problem `P5744`.
- URL: https://www.luogu.com.cn/problem/P5744
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5744_training_after_years(mut age: i32, mut score: i32, years: i32) -> i32 {
    let mut i = 0;
    while i < years { age += 1; score = score * 120 / 100; if score > 600 { score = 600; } i += 1; }
    age + score
}
```
