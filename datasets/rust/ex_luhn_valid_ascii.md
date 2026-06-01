# Exercism Luhn Valid ASCII

## Problem

Return true if `s` passes the Luhn checksum, ignoring spaces.

## Requirements

- Only digits and spaces are accepted.
- After removing spaces, length must be at least 2.

## Source

- Source: Exercism problem `luhn`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/luhn
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_luhn_valid_ascii(s: &str) -> bool {
    let mut digits = [0i32; 128]; let mut n = 0usize;
    for c in s.bytes() { if c == b' ' { continue; } if c < b'0' || c > b'9' { return false; } digits[n] = (c - b'0') as i32; n += 1; }
    if n < 2 { return false; }
    let mut sum = 0; let mut dbl = false; let mut i = n;
    while i > 0 { i -= 1; let mut v = digits[i]; if dbl { v *= 2; if v > 9 { v -= 9; } } sum += v; dbl = !dbl; }
    sum % 10 == 0
}
```
