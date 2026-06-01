# Exercism Series Largest Digit Sum

## Problem

Return the largest sum of `span` adjacent digits in `digits`.

## Requirements

- `digits` contains decimal digits only.
- `0 <= span <= length(digits)`.
- An empty span has sum `0`.

## Source

- Source: Exercism problem `series`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/series
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_series_largest_digit_sum(digits: &str, span: i32) -> i32 {
    if span == 0 { return 0; }
    let b = digits.as_bytes(); let sp = span as usize; let mut best = 0; let mut i = 0usize;
    while i + sp <= b.len() { let mut sum = 0; let mut j = 0usize; while j < sp { sum += (b[i + j] - b'0') as i32; j += 1; } if sum > best { best = sum; } i += 1; }
    best
}
```
