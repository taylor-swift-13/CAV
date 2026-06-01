# Exercism Isogram ASCII

## Problem

Return true if a phrase contains no repeated alphabetic letter, ignoring case and nonletters.

## Requirements

- Input is ASCII.
- Hyphens and spaces are ignored.

## Source

- Source: Exercism problem `isogram`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/isogram
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_isogram_ascii(s: &str) -> bool {
    let mut seen = [false; 26];
    for mut c in s.bytes() { if c >= b'A' && c <= b'Z' { c = c - b'A' + b'a'; } if c >= b'a' && c <= b'z' { let k = (c - b'a') as usize; if seen[k] { return false; } seen[k] = true; } }
    true
}
```
