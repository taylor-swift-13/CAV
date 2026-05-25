# reverse_fixed_decimal

## Problem

Return the reverse of a short decimal string, preserving every character exactly.

## Requirements

- `s` is a short ASCII decimal representation in the fixed-width style of the source beginner exercise.
- Every character is reversed, including the decimal point and any zero characters.
- No numeric parsing or normalization is allowed.
- The returned string length must equal the input string length.

## Source

- Source: Luogu problem `P5705`.
- URL: https://www.luogu.com.cn/problem/P5705
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn reverse_fixed_decimal(s: &str) -> String {
    s.chars().rev().collect()
}
```
