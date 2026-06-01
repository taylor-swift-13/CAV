# Exercism Pangram ASCII

## Problem

Return true if `s` contains every English letter at least once, ignoring case.

## Requirements

- Input is ASCII.
- Nonletters are ignored.

## Source

- Source: Exercism problem `pangram`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/pangram
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_pangram_ascii(s: &str) -> bool {
    let mut mask: i32 = 0;
    for mut c in s.bytes() { if c >= b'A' && c <= b'Z' { c = c - b'A' + b'a'; } if c >= b'a' && c <= b'z' { mask |= 1 << (c - b'a'); } }
    mask == (1 << 26) - 1
}
```
