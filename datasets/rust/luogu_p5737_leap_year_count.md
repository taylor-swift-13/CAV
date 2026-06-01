# Luogu P5737 Leap Year Count

## Problem

Return how many leap years are in the inclusive range `[start, end]`.

## Requirements

- `start <= end`.
- Use Gregorian leap-year rules.

## Source

- Source: Luogu problem `P5737`.
- URL: https://www.luogu.com.cn/problem/P5737
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5737_leap_year_count(start: i32, end: i32) -> i32 {
    let mut count = 0; let mut y = start;
    while y <= end { if y % 400 == 0 || (y % 4 == 0 && y % 100 != 0) { count += 1; } y += 1; }
    count
}
```
