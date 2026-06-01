# Luogu P5724 Range CSV

## Problem

Return the difference between the maximum and minimum value in a comma-separated integer list.

## Requirements

- `nums` is nonempty.
- Values fit in signed 32-bit integer range.

## Source

- Source: Luogu problem `P5724`.
- URL: https://www.luogu.com.cn/problem/P5724
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5724_range_csv(nums: &str) -> i32 {
    let mut mn = 0; let mut mx = 0; let mut first = true; for part in nums.split(',') { let v = part.parse::<i32>().unwrap(); if first { mn = v; mx = v; first = false; } else { if v < mn { mn = v; } if v > mx { mx = v; } } } mx - mn
}
```
