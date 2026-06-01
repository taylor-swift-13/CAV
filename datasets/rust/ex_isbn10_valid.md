# Exercism ISBN Verifier Valid

## Problem

Return true if an ISBN-10 string has exactly 10 digits after hyphen removal and a valid checksum.

## Requirements

- Hyphens are ignored.
- `X` may appear only as the final check character and has value 10.

## Source

- Source: Exercism problem `isbn-verifier`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/isbn-verifier
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_isbn10_valid(s: &str) -> bool {
    let mut pos = 0; let mut sum = 0; for ch in s.bytes() { if ch == b'-' { continue; } let v: i32; if ch == b'X' { if pos != 9 { return false; } v = 10; } else if ch >= b'0' && ch <= b'9' { v = (ch - b'0') as i32; } else { return false; } if pos >= 10 { return false; } sum += v * (10 - pos); pos += 1; } pos == 10 && sum % 11 == 0
}
```
