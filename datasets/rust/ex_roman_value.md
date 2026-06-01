# Exercism Roman Numerals Value

## Problem

Return the integer value of a valid Roman numeral string.

## Requirements

- Input is a valid Roman numeral using `I,V,X,L,C,D,M`.
- Result fits in signed 32-bit integer range.

## Source

- Source: Exercism problem `roman-numerals`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/roman-numerals
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_roman_value(s: &str) -> i32 {
    let mut sum = 0; let mut prev = 0;
    for c in s.bytes() { let v = match c { b'I' => 1, b'V' => 5, b'X' => 10, b'L' => 50, b'C' => 100, b'D' => 500, _ => 1000 }; sum += v; if prev < v { sum -= 2 * prev; } prev = v; }
    sum
}
```
