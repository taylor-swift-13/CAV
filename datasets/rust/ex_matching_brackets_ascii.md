# Exercism Matching Brackets ASCII

## Problem

Return true if brackets in `s` are correctly nested and matched.

## Requirements

- Only `()`, `[]`, and `{}` are bracket tokens.
- Other ASCII characters are ignored.

## Source

- Source: Exercism problem `matching-brackets`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/matching-brackets
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_matching_brackets_ascii(s: &str) -> bool {
    let mut st = [0u8; 128]; let mut top = 0usize;
    for c in s.bytes() { if c == b'(' || c == b'[' || c == b'{' { st[top] = c; top += 1; } else if c == b')' || c == b']' || c == b'}' { if top == 0 { return false; } top -= 1; let o = st[top]; if (c == b')' && o != b'(') || (c == b']' && o != b'[') || (c == b'}' && o != b'{') { return false; } } }
    top == 0
}
```
