# Luogu P5718 Minimum CSV

## Problem

Return the minimum value in a comma-separated integer list.

## Requirements

- `nums` is nonempty.
- Values fit in signed 32-bit integer range.

## Source

- Source: Luogu problem `P5718`.
- URL: https://www.luogu.com.cn/problem/P5718
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5718_min_csv(nums: &str) -> i32 {
    let mut best = 0; let mut first = true; for part in nums.split(',') { let v = part.parse::<i32>().unwrap(); if first || v < best { best = v; first = false; } } best
}
```
