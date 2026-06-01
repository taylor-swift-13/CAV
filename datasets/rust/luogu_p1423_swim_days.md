# Luogu P1423 Swim Days

## Problem

Return the first day on which cumulative swimming distance reaches the target distance.

## Requirements

- `x_times_100` encodes the Luogu decimal distance as `x * 100`.
- The first day distance is `2.0`; each next day is `98%` of the previous day.

## Source

- Source: Luogu problem `P1423`.
- URL: https://www.luogu.com.cn/problem/P1423
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p1423_swim_days(x_times_100: i32) -> i32 {
    let x = x_times_100 as f64 / 100.0;
    let mut sum = 0.0; let mut day_distance = 2.0; let mut days = 0; while sum < x { sum += day_distance; day_distance *= 0.98; days += 1; } days
}
```
