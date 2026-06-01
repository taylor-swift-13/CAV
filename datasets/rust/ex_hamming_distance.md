# Exercism Hamming Distance

## Problem

Return the Hamming distance between equal-length strings `a` and `b`.

## Requirements

- Inputs have equal length.
- Strings are ASCII.

## Source

- Source: Exercism problem `hamming`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/hamming
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_hamming_distance(a: &str, b: &str) -> i32 {
    let ab = a.as_bytes(); let bb = b.as_bytes(); let mut d = 0; let mut i = 0usize; while i < ab.len() { if ab[i] != bb[i] { d += 1; } i += 1; } d
}
```
