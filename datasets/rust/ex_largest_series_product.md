# Exercism Largest Series Product

## Problem

Return the largest product of `span` adjacent digits in string `digits`.

## Requirements

- `digits` contains decimal digits only.
- `0 <= span <= length(digits)`.
- An empty span has product `1`.

## Source

- Source: Exercism problem `largest-series-product`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/largest-series-product
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_largest_series_product(digits: &str, span: i32) -> i32 {
    if span == 0 { return 1; }
    let b = digits.as_bytes(); let mut best = 0; let sp = span as usize; let mut i = 0usize;
    while i + sp <= b.len() { let mut p = 1; let mut j = 0usize; while j < sp { p *= (b[i + j] - b'0') as i32; j += 1; } if p > best { best = p; } i += 1; }
    best
}
```
