# Luogu P5709 Apples Remaining

## Problem

Return how many apples remain after worms eat one apple every `t` seconds for `s` seconds.

## Requirements

- `m >= 0`, `t > 0`, and `s >= 0`.
- A partially eaten apple counts as eaten.

## Source

- Source: Luogu problem `P5709`.
- URL: https://www.luogu.com.cn/problem/P5709
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5709_apples_remaining(m: i32, t: i32, s: i32) -> i32 {
    let eaten = (s + t - 1) / t; let left = m - eaten; if left > 0 { left } else { 0 }
}
```
